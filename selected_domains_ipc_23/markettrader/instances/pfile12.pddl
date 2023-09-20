(define (problem marketcount4)
(:domain Trader)
(:objects
           Athens Edinburgh Brussels  Valencia  - market
        camel0 - camel
        Food ExpensiveRugs Coffee Cattle Water Cars GummyBears Computers LaminateFloor Copper Footballs Kittens Minerals Gold Platinum DVDs TuringMachines - goods)
(:init

        (= (price Food Athens)    5.2)
        (= (on-sale Food Athens)  12)
        (= (price ExpensiveRugs Athens)    6.8)
        (= (on-sale ExpensiveRugs Athens)  13)
        (= (price Coffee Athens)    22.3)
        (= (on-sale Coffee Athens)  11)
        (= (price Cattle Athens)    10.0)
        (= (on-sale Cattle Athens)  0)
        (= (price Water Athens)    27.2)
        (= (on-sale Water Athens)  10)
        (= (price Cars Athens)    88.0)
        (= (on-sale Cars Athens)  30)
        (= (price GummyBears Athens)    26.3)
        (= (on-sale GummyBears Athens)  0)
        (= (price Computers Athens)    78.3)
        (= (on-sale Computers Athens)  14)
        (= (price LaminateFloor Athens)    54.0)
        (= (on-sale LaminateFloor Athens)  22)
        (= (price Copper Athens)    32.3)
        (= (on-sale Copper Athens)  14)
        (= (price Footballs Athens)    65.2)
        (= (on-sale Footballs Athens)  0)
        (= (price Kittens Athens)    59.6)
        (= (on-sale Kittens Athens)  0)
        (= (price Minerals Athens)    11.6)
        (= (on-sale Minerals Athens)  56)
        (= (price Gold Athens)    37.6)
        (= (on-sale Gold Athens)  5)
        (= (price Platinum Athens)    66.0)
        (= (on-sale Platinum Athens)  61)
        (= (price DVDs Athens)    16.8)
        (= (on-sale DVDs Athens)  0)
        (= (price TuringMachines Athens)    39.2)
        (= (on-sale TuringMachines Athens)  0)

        (= (price Food Edinburgh)    4.3)
        (= (on-sale Food Edinburgh)  14)
        (= (price ExpensiveRugs Edinburgh)    6.3)
        (= (on-sale ExpensiveRugs Edinburgh)  14)
        (= (price Coffee Edinburgh)    21.2)
        (= (on-sale Coffee Edinburgh)  14)
        (= (price Cattle Edinburgh)    8.0)
        (= (on-sale Cattle Edinburgh)  0)
        (= (price Water Edinburgh)    25.2)
        (= (on-sale Water Edinburgh)  15)
        (= (price Cars Edinburgh)    91.2)
        (= (on-sale Cars Edinburgh)  22)
        (= (price GummyBears Edinburgh)    38.0)
        (= (on-sale GummyBears Edinburgh)  0)
        (= (price Computers Edinburgh)    84.0)
        (= (on-sale Computers Edinburgh)  0)
        (= (price LaminateFloor Edinburgh)    56.3)
        (= (on-sale LaminateFloor Edinburgh)  16)
        (= (price Copper Edinburgh)    32.8)
        (= (on-sale Copper Edinburgh)  13)
        (= (price Footballs Edinburgh)    70.3)
        (= (on-sale Footballs Edinburgh)  0)
        (= (price Kittens Edinburgh)    56.0)
        (= (on-sale Kittens Edinburgh)  0)
        (= (price Minerals Edinburgh)    11.2)
        (= (on-sale Minerals Edinburgh)  57)
        (= (price Gold Edinburgh)    37.2)
        (= (on-sale Gold Edinburgh)  6)
        (= (price Platinum Edinburgh)    65.2)
        (= (on-sale Platinum Edinburgh)  63)
        (= (price DVDs Edinburgh)    16.3)
        (= (on-sale DVDs Edinburgh)  0)
        (= (price TuringMachines Edinburgh)    45.2)
        (= (on-sale TuringMachines Edinburgh)  0)

        (= (price Food Brussels)    4.3)
        (= (on-sale Food Brussels)  14)
        (= (price ExpensiveRugs Brussels)    6.3)
        (= (on-sale ExpensiveRugs Brussels)  14)
        (= (price Coffee Brussels)    21.2)
        (= (on-sale Coffee Brussels)  14)
        (= (price Cattle Brussels)    8.0)
        (= (on-sale Cattle Brussels)  0)
        (= (price Water Brussels)    25.2)
        (= (on-sale Water Brussels)  15)
        (= (price Cars Brussels)    91.2)
        (= (on-sale Cars Brussels)  22)
        (= (price GummyBears Brussels)    38.0)
        (= (on-sale GummyBears Brussels)  0)
        (= (price Computers Brussels)    84.0)
        (= (on-sale Computers Brussels)  0)
        (= (price LaminateFloor Brussels)    56.3)
        (= (on-sale LaminateFloor Brussels)  16)
        (= (price Copper Brussels)    32.8)
        (= (on-sale Copper Brussels)  13)
        (= (price Footballs Brussels)    70.3)
        (= (on-sale Footballs Brussels)  0)
        (= (price Kittens  Brussels)    56.0)
        (= (on-sale Kittens  Brussels)  0)
        (= (price Minerals Brussels)    11.2)
        (= (on-sale Minerals Brussels)  57)
        (= (price Gold  Brussels)    37.2)
        (= (on-sale Gold  Brussels)  6)
        (= (price Platinum Brussels)    65.2)
        (= (on-sale Platinum Brussels)  63)
        (= (price DVDs Brussels)    16.3)
        (= (on-sale DVDs Brussels)  0)
        (= (price TuringMachines Brussels)    45.2)
        (= (on-sale TuringMachines Brussels)  0)

        (= (price Food Valencia)    2.8)
        (= (on-sale Food Valencia)  18)
        (= (price ExpensiveRugs Valencia)    5.6)
        (= (on-sale ExpensiveRugs Valencia)  16)
        (= (price Coffee Valencia)    18.8)
        (= (on-sale Coffee Valencia)  20)
        (= (price Cattle Valencia)    4.0)
        (= (on-sale Cattle Valencia)  0)
        (= (price Water Valencia)    21.2)
        (= (on-sale Water Valencia)  25)
        (= (price Cars Valencia)    97.6)
        (= (on-sale Cars Valencia)  6)
        (= (price GummyBears Valencia)    61.2)
        (= (on-sale GummyBears Valencia)  26)
        (= (price Computers Valencia)    95.2)
        (= (on-sale Computers Valencia)  0)
        (= (price LaminateFloor Valencia)    61.2)
        (= (on-sale LaminateFloor Valencia)  4)
        (= (price Copper Valencia)    33.6)
        (= (on-sale Copper Valencia)  11)
        (= (price Footballs Valencia)    80.8)
        (= (on-sale Footballs Valencia)  0)
        (= (price Kittens Valencia)    48.8)
        (= (on-sale Kittens Valencia)  18)
        (= (price Minerals Valencia)    10.3)
        (= (on-sale Minerals Valencia)  59)
        (= (price Gold Valencia)    36.3)
        (= (on-sale Gold Valencia)  8)
        (= (price Platinum Valencia)    63.6)
        (= (on-sale Platinum Valencia)  3)
        (= (price DVDs Valencia)    15.6)
        (= (on-sale DVDs Valencia)  0)
        (= (price TuringMachines Valencia)    57.2)
        (= (on-sale TuringMachines Valencia)  0)
        (= (bought Food ) 0)
        (= (bought ExpensiveRugs ) 0)
        (= (bought Coffee) 0)
        (= (bought Cattle ) 0)
        (= (bought Water ) 0)
        (= (bought Cars ) 0)
        (= (bought GummyBears ) 0)
        (= (bought Computers ) 0)
        (= (bought LaminateFloor ) 0)
        (= (bought Copper ) 0)
        (= (bought Footballs ) 0)
        (= (bought Kittens ) 0)
        (= (bought Minerals ) 0)
        (= (bought Gold ) 0)
        (= (bought Platinum ) 0)
        (= (bought DVDs ) 0)
        (= (bought TuringMachines ) 0)
        (= (drive-cost Athens Edinburgh ) 2.2)
        (= (drive-cost Edinburgh Athens ) 2.2)
        (can-drive Athens Edinburgh)
        (can-drive Edinburgh Athens)
        (= (drive-cost Athens Brussels ) 5.3)
        (= (drive-cost Brussels Athens ) 5.3)
        (can-drive Athens Brussels)
        (can-drive Brussels Athens)
        (= (drive-cost Athens Valencia ) 3.8)
        (= (drive-cost Valencia Athens ) 3.8)
        (can-drive Athens Valencia)
        (can-drive Valencia Athens)
        (= (drive-cost Edinburgh Brussels ) 6.8)
        (= (drive-cost Brussels Edinburgh ) 6.8)
        (can-drive Edinburgh Brussels)
        (can-drive Brussels Edinburgh)
        (= (drive-cost Edinburgh Valencia ) 5.3)
        (= (drive-cost Valencia Edinburgh ) 5.3)
        (can-drive Edinburgh Valencia)
        (can-drive Valencia Edinburgh)
        (= (drive-cost Brussels Valencia ) 1.6)
        (= (drive-cost Valencia Brussels ) 1.6)
        (can-drive Brussels Valencia)
        (can-drive Valencia Brussels)
        (at camel0      Valencia)
        (= (cash) 100)
        (= (capacity) 20)
        (= (fuel-used) 0)
	(= (fuel) 7.0)
)
(:goal (and
        (>= (cash) 1000)
))
;(:metric minimize (fuel-used)) 
)