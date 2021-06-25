(define (problem strips-sat-x-1)
(:domain satellite)
(:objects
	satellite0 - satellite
	instrument0 - instrument
	instrument1 - instrument
	instrument2 - instrument
	satellite1 - satellite
	instrument3 - instrument
	satellite2 - satellite
	instrument4 - instrument
	instrument5 - instrument
	instrument6 - instrument
	satellite3 - satellite
	instrument7 - instrument
	instrument8 - instrument
	satellite4 - satellite
	instrument9 - instrument
	instrument10 - instrument
	satellite5 - satellite
	instrument11 - instrument
	thermograph4 - mode
	image1 - mode
	thermograph3 - mode
	image2 - mode
	thermograph0 - mode
	groundstation3 - direction
	groundstation4 - direction
	groundstation2 - direction
	groundstation0 - direction
	groundstation1 - direction
	phenomenon5 - direction
	phenomenon6 - direction
	phenomenon7 - direction
	planet8 - direction
	star9 - direction
	star10 - direction
	phenomenon11 - direction
	phenomenon12 - direction
	phenomenon13 - direction
	star14 - direction
	planet15 - direction
	planet16 - direction
	planet17 - direction
	phenomenon18 - direction
	star19 - direction
	star20 - direction
	planet21 - direction
	star22 - direction
	planet23 - direction
	star24 - direction
)
(:init
	(supports instrument0 thermograph0)
	(supports instrument0 image1)
	(calibration_target instrument0 groundstation2)
	(supports instrument1 image2)
	(supports instrument1 thermograph3)
	(calibration_target instrument1 groundstation0)
	(supports instrument2 image1)
	(supports instrument2 thermograph3)
	(supports instrument2 thermograph4)
	(calibration_target instrument2 groundstation2)
	(on_board instrument0 satellite0)
	(on_board instrument1 satellite0)
	(on_board instrument2 satellite0)
	(power_avail satellite0)
	(pointing satellite0 phenomenon12)
	(= (data_capacity satellite0) 1000)
	(= (fuel satellite0) 133)
	(supports instrument3 thermograph0)
	(supports instrument3 thermograph4)
	(supports instrument3 image2)
	(calibration_target instrument3 groundstation2)
	(on_board instrument3 satellite1)
	(power_avail satellite1)
	(pointing satellite1 groundstation1)
	(= (data_capacity satellite1) 1000)
	(= (fuel satellite1) 133)
	(supports instrument4 thermograph4)
	(supports instrument4 image1)
	(supports instrument4 thermograph0)
	(calibration_target instrument4 groundstation1)
	(supports instrument5 thermograph4)
	(calibration_target instrument5 groundstation4)
	(supports instrument6 thermograph3)
	(supports instrument6 image1)
	(calibration_target instrument6 groundstation0)
	(on_board instrument4 satellite2)
	(on_board instrument5 satellite2)
	(on_board instrument6 satellite2)
	(power_avail satellite2)
	(pointing satellite2 groundstation2)
	(= (data_capacity satellite2) 1000)
	(= (fuel satellite2) 166)
	(supports instrument7 image2)
	(supports instrument7 thermograph3)
	(calibration_target instrument7 groundstation4)
	(supports instrument8 thermograph4)
	(supports instrument8 thermograph0)
	(calibration_target instrument8 groundstation2)
	(on_board instrument7 satellite3)
	(on_board instrument8 satellite3)
	(power_avail satellite3)
	(pointing satellite3 groundstation4)
	(= (data_capacity satellite3) 1000)
	(= (fuel satellite3) 147)
	(supports instrument9 thermograph0)
	(supports instrument9 image2)
	(supports instrument9 image1)
	(calibration_target instrument9 groundstation2)
	(supports instrument10 thermograph3)
	(supports instrument10 image1)
	(calibration_target instrument10 groundstation0)
	(on_board instrument9 satellite4)
	(on_board instrument10 satellite4)
	(power_avail satellite4)
	(pointing satellite4 planet15)
	(= (data_capacity satellite4) 1000)
	(= (fuel satellite4) 119)
	(supports instrument11 thermograph0)
	(supports instrument11 image2)
	(calibration_target instrument11 groundstation1)
	(on_board instrument11 satellite5)
	(power_avail satellite5)
	(pointing satellite5 phenomenon11)
	(= (data_capacity satellite5) 1000)
	(= (fuel satellite5) 119)
	(= (data phenomenon5 thermograph4) 170)
	(= (data phenomenon6 thermograph4) 30)
	(= (data phenomenon7 thermograph4) 84)
	(= (data planet8 thermograph4) 36)
	(= (data star9 thermograph4) 19)
	(= (data star10 thermograph4) 187)
	(= (data phenomenon11 thermograph4) 16)
	(= (data phenomenon12 thermograph4) 91)
	(= (data phenomenon13 thermograph4) 179)
	(= (data star14 thermograph4) 187)
	(= (data planet15 thermograph4) 6)
	(= (data planet16 thermograph4) 68)
	(= (data planet17 thermograph4) 178)
	(= (data phenomenon18 thermograph4) 183)
	(= (data star19 thermograph4) 50)
	(= (data star20 thermograph4) 136)
	(= (data planet21 thermograph4) 191)
	(= (data star22 thermograph4) 180)
	(= (data planet23 thermograph4) 51)
	(= (data star24 thermograph4) 64)
	(= (data phenomenon5 image1) 128)
	(= (data phenomenon6 image1) 110)
	(= (data phenomenon7 image1) 179)
	(= (data planet8 image1) 25)
	(= (data star9 image1) 2)
	(= (data star10 image1) 123)
	(= (data phenomenon11 image1) 30)
	(= (data phenomenon12 image1) 29)
	(= (data phenomenon13 image1) 75)
	(= (data star14 image1) 154)
	(= (data planet15 image1) 181)
	(= (data planet16 image1) 153)
	(= (data planet17 image1) 36)
	(= (data phenomenon18 image1) 175)
	(= (data star19 image1) 131)
	(= (data star20 image1) 94)
	(= (data planet21 image1) 106)
	(= (data star22 image1) 86)
	(= (data planet23 image1) 144)
	(= (data star24 image1) 97)
	(= (data phenomenon5 thermograph3) 30)
	(= (data phenomenon6 thermograph3) 161)
	(= (data phenomenon7 thermograph3) 185)
	(= (data planet8 thermograph3) 66)
	(= (data star9 thermograph3) 117)
	(= (data star10 thermograph3) 83)
	(= (data phenomenon11 thermograph3) 161)
	(= (data phenomenon12 thermograph3) 120)
	(= (data phenomenon13 thermograph3) 157)
	(= (data star14 thermograph3) 114)
	(= (data planet15 thermograph3) 75)
	(= (data planet16 thermograph3) 146)
	(= (data planet17 thermograph3) 57)
	(= (data phenomenon18 thermograph3) 187)
	(= (data star19 thermograph3) 22)
	(= (data star20 thermograph3) 96)
	(= (data planet21 thermograph3) 130)
	(= (data star22 thermograph3) 48)
	(= (data planet23 thermograph3) 88)
	(= (data star24 thermograph3) 151)
	(= (data phenomenon5 image2) 17)
	(= (data phenomenon6 image2) 91)
	(= (data phenomenon7 image2) 90)
	(= (data planet8 image2) 76)
	(= (data star9 image2) 65)
	(= (data star10 image2) 122)
	(= (data phenomenon11 image2) 6)
	(= (data phenomenon12 image2) 124)
	(= (data phenomenon13 image2) 17)
	(= (data star14 image2) 100)
	(= (data planet15 image2) 47)
	(= (data planet16 image2) 105)
	(= (data planet17 image2) 159)
	(= (data phenomenon18 image2) 57)
	(= (data star19 image2) 20)
	(= (data star20 image2) 32)
	(= (data planet21 image2) 183)
	(= (data star22 image2) 16)
	(= (data planet23 image2) 22)
	(= (data star24 image2) 30)
	(= (data phenomenon5 thermograph0) 25)
	(= (data phenomenon6 thermograph0) 65)
	(= (data phenomenon7 thermograph0) 131)
	(= (data planet8 thermograph0) 18)
	(= (data star9 thermograph0) 110)
	(= (data star10 thermograph0) 82)
	(= (data phenomenon11 thermograph0) 78)
	(= (data phenomenon12 thermograph0) 76)
	(= (data phenomenon13 thermograph0) 19)
	(= (data star14 thermograph0) 15)
	(= (data planet15 thermograph0) 20)
	(= (data planet16 thermograph0) 75)
	(= (data planet17 thermograph0) 148)
	(= (data phenomenon18 thermograph0) 150)
	(= (data star19 thermograph0) 55)
	(= (data star20 thermograph0) 78)
	(= (data planet21 thermograph0) 111)
	(= (data star22 thermograph0) 141)
	(= (data planet23 thermograph0) 177)
	(= (data star24 thermograph0) 174)
	(= (slew_time groundstation3 groundstation0) 45.48)
	(= (slew_time groundstation0 groundstation3) 45.48)
	(= (slew_time groundstation3 groundstation1) 17.98)
	(= (slew_time groundstation1 groundstation3) 17.98)
	(= (slew_time groundstation3 groundstation2) 27.68)
	(= (slew_time groundstation2 groundstation3) 27.68)
	(= (slew_time groundstation4 groundstation0) 5.291)
	(= (slew_time groundstation0 groundstation4) 5.291)
	(= (slew_time groundstation4 groundstation1) 27.92)
	(= (slew_time groundstation1 groundstation4) 27.92)
	(= (slew_time groundstation4 groundstation2) 2.777)
	(= (slew_time groundstation2 groundstation4) 2.777)
	(= (slew_time groundstation4 groundstation3) 53.06)
	(= (slew_time groundstation3 groundstation4) 53.06)
	(= (slew_time groundstation2 groundstation0) 10.69)
	(= (slew_time groundstation0 groundstation2) 10.69)
	(= (slew_time groundstation2 groundstation1) 3.645)
	(= (slew_time groundstation1 groundstation2) 3.645)
	(= (slew_time groundstation1 groundstation0) 35.43)
	(= (slew_time groundstation0 groundstation1) 35.43)
	(= (slew_time phenomenon5 groundstation0) 11.66)
	(= (slew_time groundstation0 phenomenon5) 11.66)
	(= (slew_time phenomenon5 groundstation1) 5.207)
	(= (slew_time groundstation1 phenomenon5) 5.207)
	(= (slew_time phenomenon5 groundstation2) 23.88)
	(= (slew_time groundstation2 phenomenon5) 23.88)
	(= (slew_time phenomenon5 groundstation3) 30.69)
	(= (slew_time groundstation3 phenomenon5) 30.69)
	(= (slew_time phenomenon5 groundstation4) 2.653)
	(= (slew_time groundstation4 phenomenon5) 2.653)
	(= (slew_time phenomenon6 groundstation0) 20.81)
	(= (slew_time groundstation0 phenomenon6) 20.81)
	(= (slew_time phenomenon6 groundstation1) 46.38)
	(= (slew_time groundstation1 phenomenon6) 46.38)
	(= (slew_time phenomenon6 groundstation2) 76.6)
	(= (slew_time groundstation2 phenomenon6) 76.6)
	(= (slew_time phenomenon6 groundstation3) 6.338)
	(= (slew_time groundstation3 phenomenon6) 6.338)
	(= (slew_time phenomenon6 groundstation4) 43.13)
	(= (slew_time groundstation4 phenomenon6) 43.13)
	(= (slew_time phenomenon6 phenomenon5) 16.46)
	(= (slew_time phenomenon5 phenomenon6) 16.46)
	(= (slew_time phenomenon7 groundstation0) 37.39)
	(= (slew_time groundstation0 phenomenon7) 37.39)
	(= (slew_time phenomenon7 groundstation1) 43.04)
	(= (slew_time groundstation1 phenomenon7) 43.04)
	(= (slew_time phenomenon7 groundstation2) 19)
	(= (slew_time groundstation2 phenomenon7) 19)
	(= (slew_time phenomenon7 groundstation3) 19.47)
	(= (slew_time groundstation3 phenomenon7) 19.47)
	(= (slew_time phenomenon7 groundstation4) 78.19)
	(= (slew_time groundstation4 phenomenon7) 78.19)
	(= (slew_time phenomenon7 phenomenon5) 5.051)
	(= (slew_time phenomenon5 phenomenon7) 5.051)
	(= (slew_time phenomenon7 phenomenon6) 0.2695)
	(= (slew_time phenomenon6 phenomenon7) 0.2695)
	(= (slew_time planet8 groundstation0) 6.021)
	(= (slew_time groundstation0 planet8) 6.021)
	(= (slew_time planet8 groundstation1) 68.61)
	(= (slew_time groundstation1 planet8) 68.61)
	(= (slew_time planet8 groundstation2) 40.02)
	(= (slew_time groundstation2 planet8) 40.02)
	(= (slew_time planet8 groundstation3) 48.99)
	(= (slew_time groundstation3 planet8) 48.99)
	(= (slew_time planet8 groundstation4) 40.91)
	(= (slew_time groundstation4 planet8) 40.91)
	(= (slew_time planet8 phenomenon5) 4.86)
	(= (slew_time phenomenon5 planet8) 4.86)
	(= (slew_time planet8 phenomenon6) 5.156)
	(= (slew_time phenomenon6 planet8) 5.156)
	(= (slew_time planet8 phenomenon7) 42.33)
	(= (slew_time phenomenon7 planet8) 42.33)
	(= (slew_time star9 groundstation0) 58.86)
	(= (slew_time groundstation0 star9) 58.86)
	(= (slew_time star9 groundstation1) 76.74)
	(= (slew_time groundstation1 star9) 76.74)
	(= (slew_time star9 groundstation2) 41.32)
	(= (slew_time groundstation2 star9) 41.32)
	(= (slew_time star9 groundstation3) 0.2021)
	(= (slew_time groundstation3 star9) 0.2021)
	(= (slew_time star9 groundstation4) 51.64)
	(= (slew_time groundstation4 star9) 51.64)
	(= (slew_time star9 phenomenon5) 11.93)
	(= (slew_time phenomenon5 star9) 11.93)
	(= (slew_time star9 phenomenon6) 32.07)
	(= (slew_time phenomenon6 star9) 32.07)
	(= (slew_time star9 phenomenon7) 7.202)
	(= (slew_time phenomenon7 star9) 7.202)
	(= (slew_time star9 planet8) 40.82)
	(= (slew_time planet8 star9) 40.82)
	(= (slew_time star10 groundstation0) 51.94)
	(= (slew_time groundstation0 star10) 51.94)
	(= (slew_time star10 groundstation1) 19.65)
	(= (slew_time groundstation1 star10) 19.65)
	(= (slew_time star10 groundstation2) 4.82)
	(= (slew_time groundstation2 star10) 4.82)
	(= (slew_time star10 groundstation3) 49.86)
	(= (slew_time groundstation3 star10) 49.86)
	(= (slew_time star10 groundstation4) 12.49)
	(= (slew_time groundstation4 star10) 12.49)
	(= (slew_time star10 phenomenon5) 11.24)
	(= (slew_time phenomenon5 star10) 11.24)
	(= (slew_time star10 phenomenon6) 21.76)
	(= (slew_time phenomenon6 star10) 21.76)
	(= (slew_time star10 phenomenon7) 3.658)
	(= (slew_time phenomenon7 star10) 3.658)
	(= (slew_time star10 planet8) 3.911)
	(= (slew_time planet8 star10) 3.911)
	(= (slew_time star10 star9) 22.92)
	(= (slew_time star9 star10) 22.92)
	(= (slew_time phenomenon11 groundstation0) 31.53)
	(= (slew_time groundstation0 phenomenon11) 31.53)
	(= (slew_time phenomenon11 groundstation1) 22.05)
	(= (slew_time groundstation1 phenomenon11) 22.05)
	(= (slew_time phenomenon11 groundstation2) 6.36)
	(= (slew_time groundstation2 phenomenon11) 6.36)
	(= (slew_time phenomenon11 groundstation3) 17.69)
	(= (slew_time groundstation3 phenomenon11) 17.69)
	(= (slew_time phenomenon11 groundstation4) 1.492)
	(= (slew_time groundstation4 phenomenon11) 1.492)
	(= (slew_time phenomenon11 phenomenon5) 22.69)
	(= (slew_time phenomenon5 phenomenon11) 22.69)
	(= (slew_time phenomenon11 phenomenon6) 4.599)
	(= (slew_time phenomenon6 phenomenon11) 4.599)
	(= (slew_time phenomenon11 phenomenon7) 9.617)
	(= (slew_time phenomenon7 phenomenon11) 9.617)
	(= (slew_time phenomenon11 planet8) 41.94)
	(= (slew_time planet8 phenomenon11) 41.94)
	(= (slew_time phenomenon11 star9) 71.15)
	(= (slew_time star9 phenomenon11) 71.15)
	(= (slew_time phenomenon11 star10) 37.34)
	(= (slew_time star10 phenomenon11) 37.34)
	(= (slew_time phenomenon12 groundstation0) 8.845)
	(= (slew_time groundstation0 phenomenon12) 8.845)
	(= (slew_time phenomenon12 groundstation1) 7.929)
	(= (slew_time groundstation1 phenomenon12) 7.929)
	(= (slew_time phenomenon12 groundstation2) 20.87)
	(= (slew_time groundstation2 phenomenon12) 20.87)
	(= (slew_time phenomenon12 groundstation3) 31.35)
	(= (slew_time groundstation3 phenomenon12) 31.35)
	(= (slew_time phenomenon12 groundstation4) 44.92)
	(= (slew_time groundstation4 phenomenon12) 44.92)
	(= (slew_time phenomenon12 phenomenon5) 78.75)
	(= (slew_time phenomenon5 phenomenon12) 78.75)
	(= (slew_time phenomenon12 phenomenon6) 33.4)
	(= (slew_time phenomenon6 phenomenon12) 33.4)
	(= (slew_time phenomenon12 phenomenon7) 14.09)
	(= (slew_time phenomenon7 phenomenon12) 14.09)
	(= (slew_time phenomenon12 planet8) 41.02)
	(= (slew_time planet8 phenomenon12) 41.02)
	(= (slew_time phenomenon12 star9) 28.21)
	(= (slew_time star9 phenomenon12) 28.21)
	(= (slew_time phenomenon12 star10) 11.69)
	(= (slew_time star10 phenomenon12) 11.69)
	(= (slew_time phenomenon12 phenomenon11) 2.542)
	(= (slew_time phenomenon11 phenomenon12) 2.542)
	(= (slew_time phenomenon13 groundstation0) 89.98)
	(= (slew_time groundstation0 phenomenon13) 89.98)
	(= (slew_time phenomenon13 groundstation1) 17.03)
	(= (slew_time groundstation1 phenomenon13) 17.03)
	(= (slew_time phenomenon13 groundstation2) 59.6)
	(= (slew_time groundstation2 phenomenon13) 59.6)
	(= (slew_time phenomenon13 groundstation3) 21.68)
	(= (slew_time groundstation3 phenomenon13) 21.68)
	(= (slew_time phenomenon13 groundstation4) 17.77)
	(= (slew_time groundstation4 phenomenon13) 17.77)
	(= (slew_time phenomenon13 phenomenon5) 69.01)
	(= (slew_time phenomenon5 phenomenon13) 69.01)
	(= (slew_time phenomenon13 phenomenon6) 40.52)
	(= (slew_time phenomenon6 phenomenon13) 40.52)
	(= (slew_time phenomenon13 phenomenon7) 6.218)
	(= (slew_time phenomenon7 phenomenon13) 6.218)
	(= (slew_time phenomenon13 planet8) 3.412)
	(= (slew_time planet8 phenomenon13) 3.412)
	(= (slew_time phenomenon13 star9) 54.48)
	(= (slew_time star9 phenomenon13) 54.48)
	(= (slew_time phenomenon13 star10) 63.14)
	(= (slew_time star10 phenomenon13) 63.14)
	(= (slew_time phenomenon13 phenomenon11) 0.5008)
	(= (slew_time phenomenon11 phenomenon13) 0.5008)
	(= (slew_time phenomenon13 phenomenon12) 18.11)
	(= (slew_time phenomenon12 phenomenon13) 18.11)
	(= (slew_time star14 groundstation0) 89.75)
	(= (slew_time groundstation0 star14) 89.75)
	(= (slew_time star14 groundstation1) 17.1)
	(= (slew_time groundstation1 star14) 17.1)
	(= (slew_time star14 groundstation2) 32.4)
	(= (slew_time groundstation2 star14) 32.4)
	(= (slew_time star14 groundstation3) 18.33)
	(= (slew_time groundstation3 star14) 18.33)
	(= (slew_time star14 groundstation4) 21.98)
	(= (slew_time groundstation4 star14) 21.98)
	(= (slew_time star14 phenomenon5) 3.812)
	(= (slew_time phenomenon5 star14) 3.812)
	(= (slew_time star14 phenomenon6) 46.63)
	(= (slew_time phenomenon6 star14) 46.63)
	(= (slew_time star14 phenomenon7) 1.334)
	(= (slew_time phenomenon7 star14) 1.334)
	(= (slew_time star14 planet8) 32.63)
	(= (slew_time planet8 star14) 32.63)
	(= (slew_time star14 star9) 50.05)
	(= (slew_time star9 star14) 50.05)
	(= (slew_time star14 star10) 15.08)
	(= (slew_time star10 star14) 15.08)
	(= (slew_time star14 phenomenon11) 83.83)
	(= (slew_time phenomenon11 star14) 83.83)
	(= (slew_time star14 phenomenon12) 85.57)
	(= (slew_time phenomenon12 star14) 85.57)
	(= (slew_time star14 phenomenon13) 8.62)
	(= (slew_time phenomenon13 star14) 8.62)
	(= (slew_time planet15 groundstation0) 88.69)
	(= (slew_time groundstation0 planet15) 88.69)
	(= (slew_time planet15 groundstation1) 11.4)
	(= (slew_time groundstation1 planet15) 11.4)
	(= (slew_time planet15 groundstation2) 35.44)
	(= (slew_time groundstation2 planet15) 35.44)
	(= (slew_time planet15 groundstation3) 14.65)
	(= (slew_time groundstation3 planet15) 14.65)
	(= (slew_time planet15 groundstation4) 68.54)
	(= (slew_time groundstation4 planet15) 68.54)
	(= (slew_time planet15 phenomenon5) 33.31)
	(= (slew_time phenomenon5 planet15) 33.31)
	(= (slew_time planet15 phenomenon6) 85.76)
	(= (slew_time phenomenon6 planet15) 85.76)
	(= (slew_time planet15 phenomenon7) 43.52)
	(= (slew_time phenomenon7 planet15) 43.52)
	(= (slew_time planet15 planet8) 47.04)
	(= (slew_time planet8 planet15) 47.04)
	(= (slew_time planet15 star9) 66.57)
	(= (slew_time star9 planet15) 66.57)
	(= (slew_time planet15 star10) 67.07)
	(= (slew_time star10 planet15) 67.07)
	(= (slew_time planet15 phenomenon11) 51.35)
	(= (slew_time phenomenon11 planet15) 51.35)
	(= (slew_time planet15 phenomenon12) 9.21)
	(= (slew_time phenomenon12 planet15) 9.21)
	(= (slew_time planet15 phenomenon13) 78.41)
	(= (slew_time phenomenon13 planet15) 78.41)
	(= (slew_time planet15 star14) 47.26)
	(= (slew_time star14 planet15) 47.26)
	(= (slew_time planet16 groundstation0) 45.71)
	(= (slew_time groundstation0 planet16) 45.71)
	(= (slew_time planet16 groundstation1) 32.37)
	(= (slew_time groundstation1 planet16) 32.37)
	(= (slew_time planet16 groundstation2) 12.93)
	(= (slew_time groundstation2 planet16) 12.93)
	(= (slew_time planet16 groundstation3) 17.66)
	(= (slew_time groundstation3 planet16) 17.66)
	(= (slew_time planet16 groundstation4) 22.13)
	(= (slew_time groundstation4 planet16) 22.13)
	(= (slew_time planet16 phenomenon5) 60.5)
	(= (slew_time phenomenon5 planet16) 60.5)
	(= (slew_time planet16 phenomenon6) 25.1)
	(= (slew_time phenomenon6 planet16) 25.1)
	(= (slew_time planet16 phenomenon7) 59.29)
	(= (slew_time phenomenon7 planet16) 59.29)
	(= (slew_time planet16 planet8) 67.74)
	(= (slew_time planet8 planet16) 67.74)
	(= (slew_time planet16 star9) 51.15)
	(= (slew_time star9 planet16) 51.15)
	(= (slew_time planet16 star10) 60.84)
	(= (slew_time star10 planet16) 60.84)
	(= (slew_time planet16 phenomenon11) 42.88)
	(= (slew_time phenomenon11 planet16) 42.88)
	(= (slew_time planet16 phenomenon12) 4.963)
	(= (slew_time phenomenon12 planet16) 4.963)
	(= (slew_time planet16 phenomenon13) 39.27)
	(= (slew_time phenomenon13 planet16) 39.27)
	(= (slew_time planet16 star14) 61.4)
	(= (slew_time star14 planet16) 61.4)
	(= (slew_time planet16 planet15) 37.14)
	(= (slew_time planet15 planet16) 37.14)
	(= (slew_time planet17 groundstation0) 39.81)
	(= (slew_time groundstation0 planet17) 39.81)
	(= (slew_time planet17 groundstation1) 7.01)
	(= (slew_time groundstation1 planet17) 7.01)
	(= (slew_time planet17 groundstation2) 9.117)
	(= (slew_time groundstation2 planet17) 9.117)
	(= (slew_time planet17 groundstation3) 13.55)
	(= (slew_time groundstation3 planet17) 13.55)
	(= (slew_time planet17 groundstation4) 30.91)
	(= (slew_time groundstation4 planet17) 30.91)
	(= (slew_time planet17 phenomenon5) 16.46)
	(= (slew_time phenomenon5 planet17) 16.46)
	(= (slew_time planet17 phenomenon6) 20.64)
	(= (slew_time phenomenon6 planet17) 20.64)
	(= (slew_time planet17 phenomenon7) 18.66)
	(= (slew_time phenomenon7 planet17) 18.66)
	(= (slew_time planet17 planet8) 57.78)
	(= (slew_time planet8 planet17) 57.78)
	(= (slew_time planet17 star9) 57.69)
	(= (slew_time star9 planet17) 57.69)
	(= (slew_time planet17 star10) 56.56)
	(= (slew_time star10 planet17) 56.56)
	(= (slew_time planet17 phenomenon11) 88.44)
	(= (slew_time phenomenon11 planet17) 88.44)
	(= (slew_time planet17 phenomenon12) 14.91)
	(= (slew_time phenomenon12 planet17) 14.91)
	(= (slew_time planet17 phenomenon13) 35.25)
	(= (slew_time phenomenon13 planet17) 35.25)
	(= (slew_time planet17 star14) 53.13)
	(= (slew_time star14 planet17) 53.13)
	(= (slew_time planet17 planet15) 20.71)
	(= (slew_time planet15 planet17) 20.71)
	(= (slew_time planet17 planet16) 24.27)
	(= (slew_time planet16 planet17) 24.27)
	(= (slew_time phenomenon18 groundstation0) 28.06)
	(= (slew_time groundstation0 phenomenon18) 28.06)
	(= (slew_time phenomenon18 groundstation1) 19.32)
	(= (slew_time groundstation1 phenomenon18) 19.32)
	(= (slew_time phenomenon18 groundstation2) 15.2)
	(= (slew_time groundstation2 phenomenon18) 15.2)
	(= (slew_time phenomenon18 groundstation3) 74.08)
	(= (slew_time groundstation3 phenomenon18) 74.08)
	(= (slew_time phenomenon18 groundstation4) 4.709)
	(= (slew_time groundstation4 phenomenon18) 4.709)
	(= (slew_time phenomenon18 phenomenon5) 10.77)
	(= (slew_time phenomenon5 phenomenon18) 10.77)
	(= (slew_time phenomenon18 phenomenon6) 14.2)
	(= (slew_time phenomenon6 phenomenon18) 14.2)
	(= (slew_time phenomenon18 phenomenon7) 13.9)
	(= (slew_time phenomenon7 phenomenon18) 13.9)
	(= (slew_time phenomenon18 planet8) 16.18)
	(= (slew_time planet8 phenomenon18) 16.18)
	(= (slew_time phenomenon18 star9) 26.29)
	(= (slew_time star9 phenomenon18) 26.29)
	(= (slew_time phenomenon18 star10) 12.61)
	(= (slew_time star10 phenomenon18) 12.61)
	(= (slew_time phenomenon18 phenomenon11) 16.65)
	(= (slew_time phenomenon11 phenomenon18) 16.65)
	(= (slew_time phenomenon18 phenomenon12) 8.913)
	(= (slew_time phenomenon12 phenomenon18) 8.913)
	(= (slew_time phenomenon18 phenomenon13) 2.08)
	(= (slew_time phenomenon13 phenomenon18) 2.08)
	(= (slew_time phenomenon18 star14) 77.58)
	(= (slew_time star14 phenomenon18) 77.58)
	(= (slew_time phenomenon18 planet15) 9.317)
	(= (slew_time planet15 phenomenon18) 9.317)
	(= (slew_time phenomenon18 planet16) 15.73)
	(= (slew_time planet16 phenomenon18) 15.73)
	(= (slew_time phenomenon18 planet17) 62.59)
	(= (slew_time planet17 phenomenon18) 62.59)
	(= (slew_time star19 groundstation0) 48.51)
	(= (slew_time groundstation0 star19) 48.51)
	(= (slew_time star19 groundstation1) 38.3)
	(= (slew_time groundstation1 star19) 38.3)
	(= (slew_time star19 groundstation2) 28.7)
	(= (slew_time groundstation2 star19) 28.7)
	(= (slew_time star19 groundstation3) 50.54)
	(= (slew_time groundstation3 star19) 50.54)
	(= (slew_time star19 groundstation4) 30.77)
	(= (slew_time groundstation4 star19) 30.77)
	(= (slew_time star19 phenomenon5) 60.95)
	(= (slew_time phenomenon5 star19) 60.95)
	(= (slew_time star19 phenomenon6) 2.464)
	(= (slew_time phenomenon6 star19) 2.464)
	(= (slew_time star19 phenomenon7) 24.32)
	(= (slew_time phenomenon7 star19) 24.32)
	(= (slew_time star19 planet8) 4.335)
	(= (slew_time planet8 star19) 4.335)
	(= (slew_time star19 star9) 76.49)
	(= (slew_time star9 star19) 76.49)
	(= (slew_time star19 star10) 81.27)
	(= (slew_time star10 star19) 81.27)
	(= (slew_time star19 phenomenon11) 63.07)
	(= (slew_time phenomenon11 star19) 63.07)
	(= (slew_time star19 phenomenon12) 37.57)
	(= (slew_time phenomenon12 star19) 37.57)
	(= (slew_time star19 phenomenon13) 57.57)
	(= (slew_time phenomenon13 star19) 57.57)
	(= (slew_time star19 star14) 27.51)
	(= (slew_time star14 star19) 27.51)
	(= (slew_time star19 planet15) 43.63)
	(= (slew_time planet15 star19) 43.63)
	(= (slew_time star19 planet16) 14.55)
	(= (slew_time planet16 star19) 14.55)
	(= (slew_time star19 planet17) 12.87)
	(= (slew_time planet17 star19) 12.87)
	(= (slew_time star19 phenomenon18) 70.64)
	(= (slew_time phenomenon18 star19) 70.64)
	(= (slew_time star20 groundstation0) 5.559)
	(= (slew_time groundstation0 star20) 5.559)
	(= (slew_time star20 groundstation1) 18.06)
	(= (slew_time groundstation1 star20) 18.06)
	(= (slew_time star20 groundstation2) 13.7)
	(= (slew_time groundstation2 star20) 13.7)
	(= (slew_time star20 groundstation3) 17.03)
	(= (slew_time groundstation3 star20) 17.03)
	(= (slew_time star20 groundstation4) 26.94)
	(= (slew_time groundstation4 star20) 26.94)
	(= (slew_time star20 phenomenon5) 13.65)
	(= (slew_time phenomenon5 star20) 13.65)
	(= (slew_time star20 phenomenon6) 37.44)
	(= (slew_time phenomenon6 star20) 37.44)
	(= (slew_time star20 phenomenon7) 38.2)
	(= (slew_time phenomenon7 star20) 38.2)
	(= (slew_time star20 planet8) 12.23)
	(= (slew_time planet8 star20) 12.23)
	(= (slew_time star20 star9) 73.66)
	(= (slew_time star9 star20) 73.66)
	(= (slew_time star20 star10) 50.51)
	(= (slew_time star10 star20) 50.51)
	(= (slew_time star20 phenomenon11) 4.401)
	(= (slew_time phenomenon11 star20) 4.401)
	(= (slew_time star20 phenomenon12) 46.45)
	(= (slew_time phenomenon12 star20) 46.45)
	(= (slew_time star20 phenomenon13) 28.36)
	(= (slew_time phenomenon13 star20) 28.36)
	(= (slew_time star20 star14) 15.61)
	(= (slew_time star14 star20) 15.61)
	(= (slew_time star20 planet15) 3.669)
	(= (slew_time planet15 star20) 3.669)
	(= (slew_time star20 planet16) 63)
	(= (slew_time planet16 star20) 63)
	(= (slew_time star20 planet17) 90.15)
	(= (slew_time planet17 star20) 90.15)
	(= (slew_time star20 phenomenon18) 25.03)
	(= (slew_time phenomenon18 star20) 25.03)
	(= (slew_time star20 star19) 5.375)
	(= (slew_time star19 star20) 5.375)
	(= (slew_time planet21 groundstation0) 5.641)
	(= (slew_time groundstation0 planet21) 5.641)
	(= (slew_time planet21 groundstation1) 0.4843)
	(= (slew_time groundstation1 planet21) 0.4843)
	(= (slew_time planet21 groundstation2) 15.42)
	(= (slew_time groundstation2 planet21) 15.42)
	(= (slew_time planet21 groundstation3) 70.52)
	(= (slew_time groundstation3 planet21) 70.52)
	(= (slew_time planet21 groundstation4) 18.26)
	(= (slew_time groundstation4 planet21) 18.26)
	(= (slew_time planet21 phenomenon5) 52.14)
	(= (slew_time phenomenon5 planet21) 52.14)
	(= (slew_time planet21 phenomenon6) 27.59)
	(= (slew_time phenomenon6 planet21) 27.59)
	(= (slew_time planet21 phenomenon7) 2.722)
	(= (slew_time phenomenon7 planet21) 2.722)
	(= (slew_time planet21 planet8) 51.94)
	(= (slew_time planet8 planet21) 51.94)
	(= (slew_time planet21 star9) 32.99)
	(= (slew_time star9 planet21) 32.99)
	(= (slew_time planet21 star10) 57.4)
	(= (slew_time star10 planet21) 57.4)
	(= (slew_time planet21 phenomenon11) 27.64)
	(= (slew_time phenomenon11 planet21) 27.64)
	(= (slew_time planet21 phenomenon12) 42.24)
	(= (slew_time phenomenon12 planet21) 42.24)
	(= (slew_time planet21 phenomenon13) 31.34)
	(= (slew_time phenomenon13 planet21) 31.34)
	(= (slew_time planet21 star14) 5.062)
	(= (slew_time star14 planet21) 5.062)
	(= (slew_time planet21 planet15) 60.38)
	(= (slew_time planet15 planet21) 60.38)
	(= (slew_time planet21 planet16) 40.32)
	(= (slew_time planet16 planet21) 40.32)
	(= (slew_time planet21 planet17) 27.68)
	(= (slew_time planet17 planet21) 27.68)
	(= (slew_time planet21 phenomenon18) 50.21)
	(= (slew_time phenomenon18 planet21) 50.21)
	(= (slew_time planet21 star19) 92.64)
	(= (slew_time star19 planet21) 92.64)
	(= (slew_time planet21 star20) 33.06)
	(= (slew_time star20 planet21) 33.06)
	(= (slew_time star22 groundstation0) 16.19)
	(= (slew_time groundstation0 star22) 16.19)
	(= (slew_time star22 groundstation1) 11.2)
	(= (slew_time groundstation1 star22) 11.2)
	(= (slew_time star22 groundstation2) 7.508)
	(= (slew_time groundstation2 star22) 7.508)
	(= (slew_time star22 groundstation3) 71.12)
	(= (slew_time groundstation3 star22) 71.12)
	(= (slew_time star22 groundstation4) 10.65)
	(= (slew_time groundstation4 star22) 10.65)
	(= (slew_time star22 phenomenon5) 79.26)
	(= (slew_time phenomenon5 star22) 79.26)
	(= (slew_time star22 phenomenon6) 37.22)
	(= (slew_time phenomenon6 star22) 37.22)
	(= (slew_time star22 phenomenon7) 72.27)
	(= (slew_time phenomenon7 star22) 72.27)
	(= (slew_time star22 planet8) 88.94)
	(= (slew_time planet8 star22) 88.94)
	(= (slew_time star22 star9) 80.32)
	(= (slew_time star9 star22) 80.32)
	(= (slew_time star22 star10) 7.131)
	(= (slew_time star10 star22) 7.131)
	(= (slew_time star22 phenomenon11) 14.67)
	(= (slew_time phenomenon11 star22) 14.67)
	(= (slew_time star22 phenomenon12) 88.02)
	(= (slew_time phenomenon12 star22) 88.02)
	(= (slew_time star22 phenomenon13) 29.61)
	(= (slew_time phenomenon13 star22) 29.61)
	(= (slew_time star22 star14) 15.47)
	(= (slew_time star14 star22) 15.47)
	(= (slew_time star22 planet15) 34.35)
	(= (slew_time planet15 star22) 34.35)
	(= (slew_time star22 planet16) 25.25)
	(= (slew_time planet16 star22) 25.25)
	(= (slew_time star22 planet17) 40.5)
	(= (slew_time planet17 star22) 40.5)
	(= (slew_time star22 phenomenon18) 29.83)
	(= (slew_time phenomenon18 star22) 29.83)
	(= (slew_time star22 star19) 48.36)
	(= (slew_time star19 star22) 48.36)
	(= (slew_time star22 star20) 34.08)
	(= (slew_time star20 star22) 34.08)
	(= (slew_time star22 planet21) 80.77)
	(= (slew_time planet21 star22) 80.77)
	(= (slew_time planet23 groundstation0) 1.317)
	(= (slew_time groundstation0 planet23) 1.317)
	(= (slew_time planet23 groundstation1) 1.922)
	(= (slew_time groundstation1 planet23) 1.922)
	(= (slew_time planet23 groundstation2) 72.41)
	(= (slew_time groundstation2 planet23) 72.41)
	(= (slew_time planet23 groundstation3) 3.206)
	(= (slew_time groundstation3 planet23) 3.206)
	(= (slew_time planet23 groundstation4) 12.94)
	(= (slew_time groundstation4 planet23) 12.94)
	(= (slew_time planet23 phenomenon5) 12.82)
	(= (slew_time phenomenon5 planet23) 12.82)
	(= (slew_time planet23 phenomenon6) 61.97)
	(= (slew_time phenomenon6 planet23) 61.97)
	(= (slew_time planet23 phenomenon7) 37.56)
	(= (slew_time phenomenon7 planet23) 37.56)
	(= (slew_time planet23 planet8) 2.773)
	(= (slew_time planet8 planet23) 2.773)
	(= (slew_time planet23 star9) 16.28)
	(= (slew_time star9 planet23) 16.28)
	(= (slew_time planet23 star10) 0.8526)
	(= (slew_time star10 planet23) 0.8526)
	(= (slew_time planet23 phenomenon11) 1.825)
	(= (slew_time phenomenon11 planet23) 1.825)
	(= (slew_time planet23 phenomenon12) 65.1)
	(= (slew_time phenomenon12 planet23) 65.1)
	(= (slew_time planet23 phenomenon13) 20.69)
	(= (slew_time phenomenon13 planet23) 20.69)
	(= (slew_time planet23 star14) 26.85)
	(= (slew_time star14 planet23) 26.85)
	(= (slew_time planet23 planet15) 19.89)
	(= (slew_time planet15 planet23) 19.89)
	(= (slew_time planet23 planet16) 15.57)
	(= (slew_time planet16 planet23) 15.57)
	(= (slew_time planet23 planet17) 13.27)
	(= (slew_time planet17 planet23) 13.27)
	(= (slew_time planet23 phenomenon18) 25.48)
	(= (slew_time phenomenon18 planet23) 25.48)
	(= (slew_time planet23 star19) 0.4137)
	(= (slew_time star19 planet23) 0.4137)
	(= (slew_time planet23 star20) 18.95)
	(= (slew_time star20 planet23) 18.95)
	(= (slew_time planet23 planet21) 5.814)
	(= (slew_time planet21 planet23) 5.814)
	(= (slew_time planet23 star22) 42)
	(= (slew_time star22 planet23) 42)
	(= (slew_time star24 groundstation0) 1.887)
	(= (slew_time groundstation0 star24) 1.887)
	(= (slew_time star24 groundstation1) 7.606)
	(= (slew_time groundstation1 star24) 7.606)
	(= (slew_time star24 groundstation2) 11.84)
	(= (slew_time groundstation2 star24) 11.84)
	(= (slew_time star24 groundstation3) 52.06)
	(= (slew_time groundstation3 star24) 52.06)
	(= (slew_time star24 groundstation4) 21.52)
	(= (slew_time groundstation4 star24) 21.52)
	(= (slew_time star24 phenomenon5) 26.96)
	(= (slew_time phenomenon5 star24) 26.96)
	(= (slew_time star24 phenomenon6) 44.28)
	(= (slew_time phenomenon6 star24) 44.28)
	(= (slew_time star24 phenomenon7) 9.921)
	(= (slew_time phenomenon7 star24) 9.921)
	(= (slew_time star24 planet8) 37.61)
	(= (slew_time planet8 star24) 37.61)
	(= (slew_time star24 star9) 0.03874)
	(= (slew_time star9 star24) 0.03874)
	(= (slew_time star24 star10) 60.49)
	(= (slew_time star10 star24) 60.49)
	(= (slew_time star24 phenomenon11) 25.4)
	(= (slew_time phenomenon11 star24) 25.4)
	(= (slew_time star24 phenomenon12) 5.084)
	(= (slew_time phenomenon12 star24) 5.084)
	(= (slew_time star24 phenomenon13) 0.9434)
	(= (slew_time phenomenon13 star24) 0.9434)
	(= (slew_time star24 star14) 89.14)
	(= (slew_time star14 star24) 89.14)
	(= (slew_time star24 planet15) 79.07)
	(= (slew_time planet15 star24) 79.07)
	(= (slew_time star24 planet16) 19.27)
	(= (slew_time planet16 star24) 19.27)
	(= (slew_time star24 planet17) 62.97)
	(= (slew_time planet17 star24) 62.97)
	(= (slew_time star24 phenomenon18) 22.59)
	(= (slew_time phenomenon18 star24) 22.59)
	(= (slew_time star24 star19) 17.42)
	(= (slew_time star19 star24) 17.42)
	(= (slew_time star24 star20) 45.27)
	(= (slew_time star20 star24) 45.27)
	(= (slew_time star24 planet21) 91.56)
	(= (slew_time planet21 star24) 91.56)
	(= (slew_time star24 star22) 52.97)
	(= (slew_time star22 star24) 52.97)
	(= (slew_time star24 planet23) 4.856)
	(= (slew_time planet23 star24) 4.856)
	(= (data-stored) 0)
	(= (fuel-used) 0)
)
(:goal (and
	(pointing satellite0 planet21)
	(pointing satellite2 star14)
	(pointing satellite5 planet17)
	(have_image phenomenon5 image1)
	(have_image phenomenon7 thermograph0)
	(have_image planet8 image2)
	(have_image star9 thermograph0)
	(have_image star10 thermograph3)
	(have_image phenomenon12 thermograph0)
	(have_image phenomenon13 image1)
	(have_image star14 thermograph4)
	(have_image planet15 image2)
	(have_image planet17 image2)
	(have_image phenomenon18 image1)
	(have_image star19 thermograph4)
	(have_image star20 thermograph4)
	(have_image planet21 thermograph0)
	(have_image star22 thermograph3)
	(have_image planet23 image1)
))
)