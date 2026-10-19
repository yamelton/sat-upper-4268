import SatFinal.PolynomialNumerics.Raw0
import SatFinal.PolynomialNumerics.Raw1
import SatFinal.PolynomialNumerics.Raw2
import SatFinal.PolynomialNumerics.Raw3
import SatFinal.PolynomialNumerics.Raw4
import SatFinal.PolynomialNumerics.Raw5
import SatFinal.PolynomialNumerics.Raw6
import SatFinal.PolynomialNumerics.Raw7
import SatFinal.PolynomialNumerics.Raw8
import SatFinal.PolynomialNumerics.Moment0
import SatFinal.PolynomialNumerics.Moment1
import SatFinal.PolynomialNumerics.Moment2
import SatFinal.PolynomialNumerics.Moment3
import SatFinal.PolynomialNumerics.Moment4
import SatFinal.PolynomialNumerics.Moment5
import SatFinal.PolynomialNumerics.Moment6
import SatFinal.PolynomialNumerics.Moment7
import SatFinal.PolynomialNumerics.Moment8
import SatFinal.PolynomialNumerics.Power0
import SatFinal.PolynomialNumerics.Power1
import SatFinal.PolynomialNumerics.Power2
import SatFinal.PolynomialNumerics.Power3
import SatFinal.PolynomialNumerics.Argument0
import SatFinal.PolynomialNumerics.Argument1
import SatFinal.PolynomialNumerics.Argument2
import SatFinal.PolynomialNumerics.Argument3
import SatFinal.PolynomialNumerics.Exp0
import SatFinal.PolynomialNumerics.Exp1
import SatFinal.PolynomialNumerics.Exp2
import SatFinal.PolynomialNumerics.Exp3
import SatFinal.PolynomialNumerics.Exp4
import SatFinal.PolynomialNumerics.Exp5
import SatFinal.PolynomialNumerics.Exp6
import SatFinal.PolynomialNumerics.Exp7
import SatFinal.PolynomialNumerics.Exp8
import SatFinal.PolynomialNumerics.Exp9
import SatFinal.PolynomialNumerics.Exp10
import SatFinal.PolynomialNumerics.Exp11
import SatFinal.PolynomialNumerics.Exp12
import SatFinal.PolynomialNumerics.Exp13
import SatFinal.PolynomialNumerics.Exp14
import SatFinal.PolynomialNumerics.Exp15
import SatFinal.PolynomialNumerics.Exp16
import SatFinal.PolynomialNumerics.Exp17
import SatFinal.PolynomialNumerics.Exp18
import SatFinal.PolynomialNumerics.Exp19
import SatFinal.PolynomialNumerics.Exp20
import SatFinal.PolynomialNumerics.Exp21
import SatFinal.PolynomialNumerics.Exp22
import SatFinal.PolynomialNumerics.Exp23
import SatFinal.PolynomialNumerics.Exp24
import SatFinal.PolynomialNumerics.Site0
import SatFinal.PolynomialNumerics.Site1
import SatFinal.PolynomialNumerics.Site2
import SatFinal.PolynomialNumerics.Site3
import SatFinal.PolynomialNumerics.Correction0
import SatFinal.PolynomialNumerics.Correction1
import SatFinal.PolynomialNumerics.Correction2
import SatFinal.PolynomialNumerics.Correction3
import SatFinal.PolynomialNumerics.Correction4
import SatFinal.PolynomialNumerics.Correction5
import SatFinal.PolynomialNumerics.Correction6
import SatFinal.PolynomialNumerics.Correction7
namespace SatFinal.PolynomialNumerics.Checks
theorem raw_steps : ∀ j : Fin 513, rawStep j := by
  intro j
  have hj := j.isLt
  match h : j.val/64 with
  | 0 =>
    have hb := raw_block_0 ⟨j.val-0, by omega⟩
    simpa only [show 0+(j.val-0) = j.val by omega] using hb
  | 1 =>
    have hb := raw_block_1 ⟨j.val-64, by omega⟩
    simpa only [show 64+(j.val-64) = j.val by omega] using hb
  | 2 =>
    have hb := raw_block_2 ⟨j.val-128, by omega⟩
    simpa only [show 128+(j.val-128) = j.val by omega] using hb
  | 3 =>
    have hb := raw_block_3 ⟨j.val-192, by omega⟩
    simpa only [show 192+(j.val-192) = j.val by omega] using hb
  | 4 =>
    have hb := raw_block_4 ⟨j.val-256, by omega⟩
    simpa only [show 256+(j.val-256) = j.val by omega] using hb
  | 5 =>
    have hb := raw_block_5 ⟨j.val-320, by omega⟩
    simpa only [show 320+(j.val-320) = j.val by omega] using hb
  | 6 =>
    have hb := raw_block_6 ⟨j.val-384, by omega⟩
    simpa only [show 384+(j.val-384) = j.val by omega] using hb
  | 7 =>
    have hb := raw_block_7 ⟨j.val-448, by omega⟩
    simpa only [show 448+(j.val-448) = j.val by omega] using hb
  | 8 =>
    have hb := raw_block_8 ⟨j.val-512, by omega⟩
    simpa only [show 512+(j.val-512) = j.val by omega] using hb
  | n+9 => omega
theorem moment_steps : ∀ j : Fin 514, momentStep j := by
  intro j
  have hj := j.isLt
  match h : j.val/64 with
  | 0 =>
    have hb := moment_block_0 ⟨j.val-0, by omega⟩
    simpa only [show 0+(j.val-0) = j.val by omega] using hb
  | 1 =>
    have hb := moment_block_1 ⟨j.val-64, by omega⟩
    simpa only [show 64+(j.val-64) = j.val by omega] using hb
  | 2 =>
    have hb := moment_block_2 ⟨j.val-128, by omega⟩
    simpa only [show 128+(j.val-128) = j.val by omega] using hb
  | 3 =>
    have hb := moment_block_3 ⟨j.val-192, by omega⟩
    simpa only [show 192+(j.val-192) = j.val by omega] using hb
  | 4 =>
    have hb := moment_block_4 ⟨j.val-256, by omega⟩
    simpa only [show 256+(j.val-256) = j.val by omega] using hb
  | 5 =>
    have hb := moment_block_5 ⟨j.val-320, by omega⟩
    simpa only [show 320+(j.val-320) = j.val by omega] using hb
  | 6 =>
    have hb := moment_block_6 ⟨j.val-384, by omega⟩
    simpa only [show 384+(j.val-384) = j.val by omega] using hb
  | 7 =>
    have hb := moment_block_7 ⟨j.val-448, by omega⟩
    simpa only [show 448+(j.val-448) = j.val by omega] using hb
  | 8 =>
    have hb := moment_block_8 ⟨j.val-512, by omega⟩
    simpa only [show 512+(j.val-512) = j.val by omega] using hb
  | n+9 => omega
theorem power_steps : ∀ j : Fin 193, powerStep j := by
  intro j
  have hj := j.isLt
  match h : j.val/64 with
  | 0 =>
    have hb := power_block_0 ⟨j.val-0, by omega⟩
    simpa only [show 0+(j.val-0) = j.val by omega] using hb
  | 1 =>
    have hb := power_block_1 ⟨j.val-64, by omega⟩
    simpa only [show 64+(j.val-64) = j.val by omega] using hb
  | 2 =>
    have hb := power_block_2 ⟨j.val-128, by omega⟩
    simpa only [show 128+(j.val-128) = j.val by omega] using hb
  | 3 =>
    have hb := power_block_3 ⟨j.val-192, by omega⟩
    simpa only [show 192+(j.val-192) = j.val by omega] using hb
  | n+4 => omega
theorem argument_steps : ∀ j : Fin 193, argumentStep j := by
  intro j
  have hj := j.isLt
  match h : j.val/64 with
  | 0 =>
    have hb := argument_block_0 ⟨j.val-0, by omega⟩
    simpa only [show 0+(j.val-0) = j.val by omega] using hb
  | 1 =>
    have hb := argument_block_1 ⟨j.val-64, by omega⟩
    simpa only [show 64+(j.val-64) = j.val by omega] using hb
  | 2 =>
    have hb := argument_block_2 ⟨j.val-128, by omega⟩
    simpa only [show 128+(j.val-128) = j.val by omega] using hb
  | 3 =>
    have hb := argument_block_3 ⟨j.val-192, by omega⟩
    simpa only [show 192+(j.val-192) = j.val by omega] using hb
  | n+4 => omega
theorem exp_steps : ∀ j : Fin 193, expStep j := by
  intro j
  have hj := j.isLt
  match h : j.val/8 with
  | 0 =>
    have hb := exp_block_0 ⟨j.val-0, by omega⟩
    simpa only [show 0+(j.val-0) = j.val by omega] using hb
  | 1 =>
    have hb := exp_block_1 ⟨j.val-8, by omega⟩
    simpa only [show 8+(j.val-8) = j.val by omega] using hb
  | 2 =>
    have hb := exp_block_2 ⟨j.val-16, by omega⟩
    simpa only [show 16+(j.val-16) = j.val by omega] using hb
  | 3 =>
    have hb := exp_block_3 ⟨j.val-24, by omega⟩
    simpa only [show 24+(j.val-24) = j.val by omega] using hb
  | 4 =>
    have hb := exp_block_4 ⟨j.val-32, by omega⟩
    simpa only [show 32+(j.val-32) = j.val by omega] using hb
  | 5 =>
    have hb := exp_block_5 ⟨j.val-40, by omega⟩
    simpa only [show 40+(j.val-40) = j.val by omega] using hb
  | 6 =>
    have hb := exp_block_6 ⟨j.val-48, by omega⟩
    simpa only [show 48+(j.val-48) = j.val by omega] using hb
  | 7 =>
    have hb := exp_block_7 ⟨j.val-56, by omega⟩
    simpa only [show 56+(j.val-56) = j.val by omega] using hb
  | 8 =>
    have hb := exp_block_8 ⟨j.val-64, by omega⟩
    simpa only [show 64+(j.val-64) = j.val by omega] using hb
  | 9 =>
    have hb := exp_block_9 ⟨j.val-72, by omega⟩
    simpa only [show 72+(j.val-72) = j.val by omega] using hb
  | 10 =>
    have hb := exp_block_10 ⟨j.val-80, by omega⟩
    simpa only [show 80+(j.val-80) = j.val by omega] using hb
  | 11 =>
    have hb := exp_block_11 ⟨j.val-88, by omega⟩
    simpa only [show 88+(j.val-88) = j.val by omega] using hb
  | 12 =>
    have hb := exp_block_12 ⟨j.val-96, by omega⟩
    simpa only [show 96+(j.val-96) = j.val by omega] using hb
  | 13 =>
    have hb := exp_block_13 ⟨j.val-104, by omega⟩
    simpa only [show 104+(j.val-104) = j.val by omega] using hb
  | 14 =>
    have hb := exp_block_14 ⟨j.val-112, by omega⟩
    simpa only [show 112+(j.val-112) = j.val by omega] using hb
  | 15 =>
    have hb := exp_block_15 ⟨j.val-120, by omega⟩
    simpa only [show 120+(j.val-120) = j.val by omega] using hb
  | 16 =>
    have hb := exp_block_16 ⟨j.val-128, by omega⟩
    simpa only [show 128+(j.val-128) = j.val by omega] using hb
  | 17 =>
    have hb := exp_block_17 ⟨j.val-136, by omega⟩
    simpa only [show 136+(j.val-136) = j.val by omega] using hb
  | 18 =>
    have hb := exp_block_18 ⟨j.val-144, by omega⟩
    simpa only [show 144+(j.val-144) = j.val by omega] using hb
  | 19 =>
    have hb := exp_block_19 ⟨j.val-152, by omega⟩
    simpa only [show 152+(j.val-152) = j.val by omega] using hb
  | 20 =>
    have hb := exp_block_20 ⟨j.val-160, by omega⟩
    simpa only [show 160+(j.val-160) = j.val by omega] using hb
  | 21 =>
    have hb := exp_block_21 ⟨j.val-168, by omega⟩
    simpa only [show 168+(j.val-168) = j.val by omega] using hb
  | 22 =>
    have hb := exp_block_22 ⟨j.val-176, by omega⟩
    simpa only [show 176+(j.val-176) = j.val by omega] using hb
  | 23 =>
    have hb := exp_block_23 ⟨j.val-184, by omega⟩
    simpa only [show 184+(j.val-184) = j.val by omega] using hb
  | 24 =>
    have hb := exp_block_24 ⟨j.val-192, by omega⟩
    simpa only [show 192+(j.val-192) = j.val by omega] using hb
  | n+25 => omega
theorem site_steps : ∀ j : Fin 193, siteStep j := by
  intro j
  have hj := j.isLt
  match h : j.val/64 with
  | 0 =>
    have hb := site_block_0 ⟨j.val-0, by omega⟩
    simpa only [show 0+(j.val-0) = j.val by omega] using hb
  | 1 =>
    have hb := site_block_1 ⟨j.val-64, by omega⟩
    simpa only [show 64+(j.val-64) = j.val by omega] using hb
  | 2 =>
    have hb := site_block_2 ⟨j.val-128, by omega⟩
    simpa only [show 128+(j.val-128) = j.val by omega] using hb
  | 3 =>
    have hb := site_block_3 ⟨j.val-192, by omega⟩
    simpa only [show 192+(j.val-192) = j.val by omega] using hb
  | n+4 => omega
theorem correction_steps : ∀ j : Fin 512, correctionStep j := by
  intro j
  have hj := j.isLt
  match h : j.val/64 with
  | 0 =>
    have hb := correction_block_0 ⟨j.val-0, by omega⟩
    simpa only [show 0+(j.val-0) = j.val by omega] using hb
  | 1 =>
    have hb := correction_block_1 ⟨j.val-64, by omega⟩
    simpa only [show 64+(j.val-64) = j.val by omega] using hb
  | 2 =>
    have hb := correction_block_2 ⟨j.val-128, by omega⟩
    simpa only [show 128+(j.val-128) = j.val by omega] using hb
  | 3 =>
    have hb := correction_block_3 ⟨j.val-192, by omega⟩
    simpa only [show 192+(j.val-192) = j.val by omega] using hb
  | 4 =>
    have hb := correction_block_4 ⟨j.val-256, by omega⟩
    simpa only [show 256+(j.val-256) = j.val by omega] using hb
  | 5 =>
    have hb := correction_block_5 ⟨j.val-320, by omega⟩
    simpa only [show 320+(j.val-320) = j.val by omega] using hb
  | 6 =>
    have hb := correction_block_6 ⟨j.val-384, by omega⟩
    simpa only [show 384+(j.val-384) = j.val by omega] using hb
  | 7 =>
    have hb := correction_block_7 ⟨j.val-448, by omega⟩
    simpa only [show 448+(j.val-448) = j.val by omega] using hb
  | n+8 => omega
end SatFinal.PolynomialNumerics.Checks
