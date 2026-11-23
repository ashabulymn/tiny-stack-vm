// tiny-stack-vm: interpreter for make.fun's tiny stack ISA (kit: generator/subject/ISA.md).
// One run answers a whole set: for each instance it writes the bytes printed and the exit code.
//   MAKEFUN_INPUT_DIR=practice/input MAKEFUN_OUTPUT_DIR=out node main.ts
// Node 22, standard library only.
import {mkdirSync,readdirSync,readFileSync,writeFileSync} from 'node:fs';
import {join} from 'node:path';

// Runs one program on its input bytes: the bytes it wrote and the code it ended with
// (0 for HALT, EXIT's low byte, or a trap's code).
function run(p:Uint8Array,inp:Uint8Array):{out:Uint8Array,code:number}{
 const S=new Int32Array(256);let sp=0;
 const C=new Int32Array(64);let cp=0;
 const M=new Int32Array(256);
 const O=new Uint8Array(65536);let ol=0,pc=0,ip=0,st=0;
 const fin=(c:number)=>({out:O.slice(0,ol),code:c});
 for(;;){
  if(st===1e6)return fin(10);
  if(pc<0||pc>=p.length)return fin(9);
  const op=p[pc];
  // Opcodes the ISA names: 00-07, 10-22, 30-34, 40-41, 50-53.
  const known=op<=7||(op>=0x10&&op<=0x22)||(op>=0x30&&op<=0x34)||(op>=0x40&&op<=0x41)||(op>=0x50&&op<=0x53);
  if(!known)return fin(5);
  // Immediate lengths: PUSH8 1, PUSH32 4, JMP/JZ/JNZ/CALL 2, the rest 0.
  const im=op===1?1:op===2?4:op>=0x30&&op<=0x33?2:0;
  if(pc+im>=p.length)return fin(9);
  st++;
  const nx=pc+1+im;
  // How many values this instruction pops and pushes, for the stack bounds.
  let pops=0,push=0;
  if(op===3||op===4||op===0x17||op===0x1b||op===0x31||op===0x32||op===0x40||op===0x50||op===0x51||op===0x53)pops=1;
  else if(op===5||op===6||op===0x41)pops=2;
  else if(op===7)pops=3;
  else if(op>=0x10&&op<=0x22&&op!==0x17&&op!==0x1b)pops=2;
  if(op===1||op===2||op===0x52||op===0x17||op===0x1b||op===0x40)push=1;
  else if(op===4||op===5)push=2;
  else if(op===6||op===7)push=3;
  else if(op>=0x10&&op<=0x22&&op!==0x17&&op!==0x1b)push=1;
  if(sp<pops)return fin(2);
  if(sp-pops+push>256)return fin(3);
  pc=nx;
  // The two-operand arithmetic, comparison and shift instructions.
  if(op>=0x10&&op<=0x22&&op!==0x17&&op!==0x1b){
   const b=S[sp-1],a=S[sp-2];let r=0;
   if(op===0x10)r=(a+b)|0;
   else if(op===0x11)r=(a-b)|0;
   else if(op===0x12)r=Math.imul(a,b);
   else if(op===0x13){if(b===0)return fin(4);r=a===-2147483648&&b===-1?a:(a/b)|0;}
   else if(op===0x14){if(b===0)return fin(4);r=b===-1?0:(a%b)|0;}
   else if(op===0x15){if(b===0)return fin(4);r=Math.floor((a>>>0)/(b>>>0))|0;}
   else if(op===0x16){if(b===0)return fin(4);r=((a>>>0)%(b>>>0))|0;}
   else if(op===0x18)r=a&b;
   else if(op===0x19)r=a|b;
   else if(op===0x1a)r=a^b;
   else if(op===0x1c)r=a<<(b&31);
   else if(op===0x1d)r=a>>(b&31);
   else if(op===0x1e)r=(a>>>(b&31))|0;
   else if(op===0x20)r=a===b?1:0;
   else if(op===0x21)r=a<b?1:0;
   else if(op===0x22)r=(a>>>0)<(b>>>0)?1:0;
   sp-=2;S[sp++]=r;continue;
  }
  switch(op){
   case 0:return fin(0);
   case 1:S[sp++]=(p[nx-1]<<24)>>24;break;
   case 2:S[sp++]=p[nx-4]|(p[nx-3]<<8)|(p[nx-2]<<16)|(p[nx-1]<<24);break;
   case 3:sp--;break;
   case 4:S[sp]=S[sp-1];sp++;break;
   case 5:{const t=S[sp-1];S[sp-1]=S[sp-2];S[sp-2]=t;break;}
   case 6:S[sp]=S[sp-2];sp++;break;
   case 7:{const a=S[sp-3];S[sp-3]=S[sp-2];S[sp-2]=S[sp-1];S[sp-1]=a;break;}
   case 0x17:S[sp-1]=-S[sp-1]|0;break;
   case 0x1b:S[sp-1]=~S[sp-1];break;
   case 0x30:{const rel=((p[nx-2]|(p[nx-1]<<8))<<16)>>16;pc=nx+rel;break;}
   case 0x31:case 0x32:{const rel=((p[nx-2]|(p[nx-1]<<8))<<16)>>16;const v=S[--sp];if((op===0x31)===(v===0))pc=nx+rel;break;}
   case 0x33:if(cp===64)return fin(7);C[cp++]=nx;pc=p[nx-2]|(p[nx-1]<<8);break;
   case 0x34:if(!cp)return fin(8);pc=C[--cp];break;
   case 0x40:{const a=S[sp-1];if(a<0||a>=256)return fin(6);S[sp-1]=M[a];break;}
   case 0x41:{const a=S[sp-1],v=S[sp-2];if(a<0||a>=256)return fin(6);sp-=2;M[a]=v;break;}
   case 0x50:{const t=String(S[sp-1]);if(ol+t.length>65536)return fin(11);sp--;for(let i=0;i<t.length;i++)O[ol++]=t.charCodeAt(i);break;}
   case 0x51:if(ol+1>65536)return fin(11);O[ol++]=S[--sp]&255;break;
   case 0x52:S[sp++]=ip<inp.length?inp[ip++]:-1;break;
   case 0x53:return fin(S[--sp]&255);
  }
 }
}
const I=process.env.MAKEFUN_INPUT_DIR??'/input';
const O=process.env.MAKEFUN_OUTPUT_DIR??'/output';
for(const id of readdirSync(I).sort()){
 const r=run(new Uint8Array(readFileSync(join(I,id,'program.bin'))),new Uint8Array(readFileSync(join(I,id,'input.bin'))));
 mkdirSync(join(O,id),{recursive:true});
 writeFileSync(join(O,id,'stdout.bin'),r.out);
 writeFileSync(join(O,id,'exit.txt'),`${r.code}\n`);
}
