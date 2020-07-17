/*
  Splitting seconds into hours, minutes and seconds.
  Original example from "Kuncak, Mayer, Piskac, Suter: Complete Functional Synthesis (PLDI'10)"
*/

// Split totsec seconds into hours, minutes and seconds
procedure Split(totsec: int) returns (hours, minutes, seconds: int);
  requires totsec >= 0;
  ensures hours * 3600 + minutes * 60 + seconds == totsec;
  ensures 0 <= seconds && seconds < 60;
  ensures 0 <= minutes && minutes < 60;

// Example calls to Split
procedure main() returns (hours1, minutes1, seconds1,
                          hours2, minutes2, seconds2,
                          hours3, minutes3, seconds3: int)
{
  call hours1, minutes1, seconds1 := Split(0);
  call hours2, minutes2, seconds2 := Split(11720);     // 3 h 15 min 20 sec
  call hours3, minutes3, seconds3 := Split(31536000);  // a year
}
