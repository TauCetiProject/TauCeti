/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.RepresentationTheory.LSPath.Stretch
import TauCeti.GroupTheory.Coxeter.ChainProperty
import TauCeti.Data.Rat.NumDenDvd

/-!
# Clearing the breaks of a rational Bruhat-chain path

A decreasing sequence in the parabolic Bruhat quotient, together with rational break times,
need not encode an LS path: the breaks may fail the bond-integrality conditions. Multiplying
the shape by a positive common multiple of the break denominators removes this obstruction.
The stabilizer quotient is unchanged, and each bond is multiplied by that same integer.

`LSPath.ofBruhatChain` constructs the resulting LS encoding, retaining the original directions
and times. `LSPath.toPLPath_ofBruhatChain` identifies its realization with the linear dilation
of the original rationally timed orbit path. In particular,
`LSPath.exists_toPLPath_eq_dilation_of_bruhatChain` requires no integrality assumption on the
original breaks. This supplies rational decreasing orbit paths for stretching and linking
arguments; it does not assert root-operator similarity or membership in the straight-path
component.

The construction does not require a regular or even dominant shape. The directions are actual
minimal representatives for its wall parabolic. A single direction, zero shape, and empty root
systems are allowed; no internal break requires an arbitrary extra direction in these cases.

## References

* P. Littelmann, *Paths and root operators in representation theory*, Ann. of Math. 142 (1995),
  §§4–5 (LS chains and stretching).
-/

public section

namespace TauCeti.LSPath

open RootPairing

variable {ι M N : Type*} [AddCommGroup M] [AddCommGroup N]
  {P : RootPairing ι ℤ M N} {b : P.Base} [Finite ι] [P.IsReduced] {lam : M} {l : ℕ}

/-- Construct an LS path from strictly decreasing parabolic Bruhat directions and rational
breaks by multiplying the shape by a positive common multiple of the internal break
denominators. The directions and break times are unchanged. -/
noncomputable def ofBruhatChain
    (dir : Fin (l + 1) →
      {w // (weylCoxeterSystem P b).IsMinimalCosetRep (P.wallIndices b lam) w})
    (hdir : ∀ j : Fin l,
      (weylCoxeterSystem P b).BruhatLE (dir j.succ).1 (dir j.castSucc).1)
    (hne : ∀ j : Fin l, dir j.succ ≠ dir j.castSucc)
    (time : Fin (l + 2) → ℚ) (hzero : time 0 = 0) (hlast : time (Fin.last _) = 1)
    (htime : StrictMono time) (n : ℕ) (hn : 0 < n)
    (hden : ∀ j : Fin l, (time j.castSucc.succ).den ∣ n) : LSPath P b (n • lam) := by
  let liftDir := P.minimalCosetRepNsmulEquiv b lam n hn.ne'
  let dir' := fun j ↦ liftDir (dir j)
  -- The directions are already distinct at adjacent breaks and the times strictly increase.
  -- Retain these exact indexed data rather than normalizing a list of segments.
  refine
    { length := l
      dir := dir'
      time := time
      time_zero := hzero
      time_last := hlast
      strictMono_time := htime
      dir_succ_ne := fun j h ↦ hne j (liftDir.injective h)
      exists_isAChain := ?_ }
  intro j
  obtain ⟨C, hhead, hlast⟩ := CoxeterSystem.exists_minimalCosetRepChain
    (dir' j.succ).2 (dir' j.castSucc).2
    (by simpa only [dir', liftDir, coe_minimalCosetRepNsmulEquiv] using hdir j)
  refine ⟨C, hhead, hlast, isAChain_iff_forall_reflectionBond.mpr fun k ↦ ?_⟩
  obtain ⟨z, hz⟩ := (Rat.den_dvd_iff_exists_mul_intCast_eq (time j.castSucc.succ) (n : ℤ)).mp
    (by exact_mod_cast hden j)
  refine ⟨z * P.reflectionBond b ((C k.castSucc).1 • lam) ((C k.succ).1 • lam), ?_⟩
  rw [P.reflectionBond_smul_nsmul b]
  push_cast at hz ⊢
  rw [← mul_assoc, hz]

variable
    (dir : Fin (l + 1) →
      {w // (weylCoxeterSystem P b).IsMinimalCosetRep (P.wallIndices b lam) w})
    (hdir : ∀ j : Fin l,
      (weylCoxeterSystem P b).BruhatLE (dir j.succ).1 (dir j.castSucc).1)
    (hne : ∀ j : Fin l, dir j.succ ≠ dir j.castSucc)
    (time : Fin (l + 2) → ℚ) (hzero : time 0 = 0) (hlast : time (Fin.last _) = 1)
    (htime : StrictMono time) (n : ℕ) (hn : 0 < n)
    (hden : ∀ j : Fin l, (time j.castSucc.succ).den ∣ n)

/-- Clearing break denominators introduces no additional directions. -/
@[simp]
theorem length_ofBruhatChain :
    (ofBruhatChain dir hdir hne time hzero hlast htime n hn hden).length = l := (rfl)

/-- The directions remain the same Weyl-group elements after scaling the shape. -/
@[simp]
theorem dir_ofBruhatChain
    (j : Fin ((ofBruhatChain dir hdir hne time hzero hlast htime n hn hden).length + 1)) :
    ((ofBruhatChain dir hdir hne time hzero hlast htime n hn hden).dir j).1 =
      (dir (j.cast (congrArg (· + 1)
        (length_ofBruhatChain dir hdir hne time hzero hlast htime n hn hden)))).1 := by
  simp only [ofBruhatChain, coe_minimalCosetRepNsmulEquiv]
  exact congrArg (fun k ↦ (dir k).1) (Fin.ext rfl)

/-- Clearing break denominators retains every break time, including the endpoints. -/
@[simp]
theorem time_ofBruhatChain
    (j : Fin ((ofBruhatChain dir hdir hne time hzero hlast htime n hn hden).length + 2)) :
    (ofBruhatChain dir hdir hne time hzero hlast htime n hn hden).time j =
      time (j.cast (congrArg (· + 2)
        (length_ofBruhatChain dir hdir hne time hzero hlast htime n hn hden))) := (rfl)

/-- The constructed LS path traverses each direction for its original duration. -/
@[simp]
theorem duration_ofBruhatChain
    (j : Fin ((ofBruhatChain dir hdir hne time hzero hlast htime n hn hden).length + 1)) :
    (ofBruhatChain dir hdir hne time hzero hlast htime n hn hden).duration j =
      time (j.cast (congrArg (· + 1)
        (length_ofBruhatChain dir hdir hne time hzero hlast htime n hn hden))).succ -
      time (j.cast (congrArg (· + 1)
        (length_ofBruhatChain dir hdir hne time hzero hlast htime n hn hden))).castSucc := by
  simp only [duration_def, time_ofBruhatChain]
  -- Casting preserves index values and hence commutes with the two duration endpoints.
  rfl

section Realization

variable (𝕜 : Type*) {V : Type*} [Field 𝕜] [LinearOrder 𝕜] [IsStrictOrderedRing 𝕜]
  [AddCommGroup V] [Module 𝕜 V] (f : M →+ V)

omit [LinearOrder 𝕜] [IsStrictOrderedRing 𝕜] in
/-- The constructed LS path retains the rational durations and dilates each original orbit
segment by the chosen common denominator. This compares parametrized presentations. -/
theorem timed_ofBruhatChain :
    (ofBruhatChain dir hdir hne time hzero hlast htime n hn hden).timed 𝕜 f =
      List.ofFn (fun j : Fin (l + 1) ↦
        (((time j.succ - time j.castSucc : ℚ) : 𝕜),
          (n : 𝕜) • (((time j.succ - time j.castSucc : ℚ) : 𝕜) • f ((dir j).1 • lam)))) := by
  simp only [timed_def]
  rw [List.ofFn_congr (congrArg (· + 1)
    (length_ofBruhatChain dir hdir hne time hzero hlast htime n hn hden))]
  simp only [duration_ofBruhatChain, dir_ofBruhatChain, Fin.cast_cast, Fin.cast_eq_self,
    smul_comm _ n lam, map_nsmul]
  congr 1
  funext j
  rw [← Nat.cast_smul_eq_nsmul 𝕜, smul_comm]

/-- The realization is the dilation of the original rational Bruhat-chain path, as an actual
path modulo reparametrization, rather than merely an equality of endpoints. -/
theorem toPLPath_ofBruhatChain :
    (ofBruhatChain dir hdir hne time hzero hlast htime n hn hden).toPLPath 𝕜 f =
      (PLPath.ofSegments 𝕜 (List.ofFn fun j : Fin (l + 1) ↦
        ((time j.succ - time j.castSucc : ℚ) : 𝕜) • f ((dir j).1 • lam))).map
          ((n : 𝕜) • LinearMap.id) := by
  simp only [toPLPath_def, timed_ofBruhatChain, PLPath.map_ofSegments, List.map_ofFn,
    Function.comp_def, LinearMap.smul_apply, LinearMap.id_apply]

include hdir hne hzero hlast htime in
/-- Every rationally timed strictly decreasing parabolic Bruhat-chain path becomes an LS path
of a positive multiple of its shape after dilation. No initial break-integrality condition is
assumed. A product of the internal break denominators is a valid stretching factor. -/
theorem exists_toPLPath_eq_dilation_of_bruhatChain :
    ∃ n : ℕ, 0 < n ∧ ∃ π : LSPath P b (n • lam),
      π.toPLPath 𝕜 f =
        (PLPath.ofSegments 𝕜 (List.ofFn fun j : Fin (l + 1) ↦
          ((time j.succ - time j.castSucc : ℚ) : 𝕜) • f ((dir j).1 • lam))).map
            ((n : 𝕜) • LinearMap.id) := by
  let n := ∏ j : Fin l, (time j.castSucc.succ).den
  have hn : 0 < n := Finset.prod_pos fun j _ ↦ (time j.castSucc.succ).den_pos
  have hden (j : Fin l) : (time j.castSucc.succ).den ∣ n :=
    Finset.dvd_prod_of_mem _ (Finset.mem_univ j)
  exact ⟨n, hn, ofBruhatChain dir hdir hne time hzero hlast htime n hn hden,
    toPLPath_ofBruhatChain dir hdir hne time hzero hlast htime n hn hden 𝕜 f⟩

end Realization

end TauCeti.LSPath
