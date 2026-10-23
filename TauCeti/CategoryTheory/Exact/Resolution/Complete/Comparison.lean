/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.Algebra.Homology.Homotopy
public import TauCeti.CategoryTheory.Exact.Resolution.Complete.Basic

/-!
# The comparison theorem for complete resolutions

Complete resolutions, `TauCeti.ExactStructure.CompleteResolution`, are bi-infinite sequences of
conflations `Zⁿ ↪ Xⁿ ↠ Zⁿ⁺¹` with projective-injective middle terms, spliced into a cochain
complex. This file proves that they are unique up to homotopy.

Let `r` and `r'` be complete resolutions and `f : r.Z 0 ⟶ r'.Z 0`. Then `f` lifts to a map of
complexes `lift f`. In negative degrees the lift is built downwards, lifting along the deflations
of `r'` out of the projective terms of `r`; in nonnegative degrees it is built upwards, extending
across the inflations of `r` into the injective terms of `r'`.

A map of complexes lifting `f` is null-homotopic exactly when `f` factors through a
projective-injective object. When `E` is Frobenius, the projective-injective objects are the
relative projectives, so this says that `f` vanishes in `E.ProjectiveStableCategory`. In
particular two lifts of the same morphism are homotopic, and two complete resolutions with
isomorphic objects of cycles in degree zero are homotopy equivalent. In a Frobenius exact
category every object has a complete resolution, so complete resolutions are unique up to
homotopy equivalence.

No Frobenius hypothesis is needed for the comparison theorem itself: the projectivity and
injectivity of the terms of the two resolutions are all it uses.

## Main definitions

* `TauCeti.ExactStructure.CompleteResolution.lift`: the map of complexes lifting a morphism of the
  objects of cycles in degree zero.
* `TauCeti.ExactStructure.CompleteResolution.liftHomotopyZero`: a map of complexes lifting a
  morphism that factors through a projective-injective object is null-homotopic.
* `TauCeti.ExactStructure.CompleteResolution.liftHomotopy`: two lifts of the same morphism are
  homotopic.
* `TauCeti.ExactStructure.CompleteResolution.homotopyEquiv`: complete resolutions with isomorphic
  objects of cycles in degree zero are homotopy equivalent.

## Main results

* `TauCeti.ExactStructure.CompleteResolution.ι_lift_f_zero`: the lift induces `f` on the objects of
  cycles in degree zero.
* `TauCeti.ExactStructure.CompleteResolution.nonempty_homotopy_zero_iff`: a map of complexes lifting
  `f` is null-homotopic if and only if `f` factors through a projective-injective object.

## References

* Ragnar-Olaf Buchweitz, *Maximal Cohen–Macaulay Modules and Tate Cohomology*, Section 4, for
  complete resolutions and their uniqueness up to homotopy.
* Theo Bühler, *Exact categories*, Expositiones Mathematicae **28** (2010), 1--69, Section 12, for
  the comparison theorem for projective resolutions in an exact category.
* `Mathlib/CategoryTheory/Abelian/Projective/Resolution.lean`, whose `lift`, `liftHomotopyZero`,
  `liftHomotopy`, `liftIdHomotopy`, `liftCompHomotopy` and `homotopyEquiv` API for projective
  resolutions in abelian categories is followed here, including the derivation of
  `liftHomotopy` from `liftHomotopyZero` through `Homotopy.equivSubZero`, and the construction of
  the lift and of the null-homotopy from a base case and a repeated step.
* `Mathlib/CategoryTheory/Abelian/Injective/Resolution.lean`, the dual comparison theory for
  injective resolutions, which the upward half of the construction follows.
* `TauCeti/CategoryTheory/Exact/Resolution/Comparison.lean`, the comparison theorem for finite
  projective resolutions in an exact category (`TauCeti.ExactStructure.FiniteResolution.lift`,
  `liftHomotopy`, `homotopyEquiv`), of which this is the bi-infinite analogue.
-/

public section

namespace TauCeti

open CategoryTheory CategoryTheory.Limits

universe v u

variable {C : Type u} [Category.{v} C] [Preadditive C] [HasZeroObject C] [HasBinaryBiproducts C]

namespace ExactStructure

namespace CompleteResolution

variable {E : ExactStructure C} {r r' : E.CompleteResolution}

section Lift

/-! ### The lift

The lift is assembled from the comparison maps of presentations. Each conflation
`Zⁿ ↪ Xⁿ ↠ Zⁿ⁺¹` is an injective presentation of `Zⁿ` and a projective presentation of `Zⁿ⁺¹`.
Upwards, a map `Zⁿ ⟶ Z'ⁿ` extends to the injective middle terms and induces a map `Zⁿ⁺¹ ⟶ Z'ⁿ⁺¹`
on cokernels (`InjectivePresentation.middleMap` and `cokernelMap`). Downwards, a map
`Zⁿ⁺¹ ⟶ Z'ⁿ⁺¹` lifts to the projective middle terms and induces a map `Zⁿ ⟶ Z'ⁿ` on kernels
(`ProjectivePresentation.middleMap` and `kernelMap`). -/

variable (r r')

/-- The components on cycles of the lift in nonnegative degrees, by upward steps from `f`. -/
private noncomputable def liftPos (f : r.Z 0 ⟶ r'.Z 0) : ∀ k : ℕ, r.Z k ⟶ r'.Z k
  | 0 => f
  | k + 1 => (r.injectivePresentation k).cokernelMap (r'.injectivePresentation k) (liftPos f k)

/-- The components on cycles of the lift in nonpositive degrees, by downward steps from `f`;
`liftNeg f k` is the component in degree `Int.negSucc k + 1`. -/
private noncomputable def liftNeg (f : r.Z 0 ⟶ r'.Z 0) :
    ∀ k : ℕ, r.Z (Int.negSucc k + 1) ⟶ r'.Z (Int.negSucc k + 1)
  | 0 => f
  | k + 1 => (r.projectivePresentation (Int.negSucc k)).kernelMap
      (r'.projectivePresentation (Int.negSucc k)) (liftNeg f k)

/-- The components on cycles of the lift. -/
private noncomputable def liftZ' (f : r.Z 0 ⟶ r'.Z 0) : ∀ n : ℤ, r.Z n ⟶ r'.Z n
  | Int.ofNat k => liftPos r r' f k
  | Int.negSucc k => liftNeg r r' f (k + 1)

/-- The components on terms of the lift. -/
private noncomputable def liftX (f : r.Z 0 ⟶ r'.Z 0) : ∀ n : ℤ, r.X n ⟶ r'.X n
  | Int.ofNat k => (r.injectivePresentation (Int.ofNat k)).middleMap
      (r'.injectivePresentation (Int.ofNat k)) (liftPos r r' f k)
  | Int.negSucc k => (r.projectivePresentation (Int.negSucc k)).middleMap
      (r'.projectivePresentation (Int.negSucc k)) (liftNeg r r' f k)

/-! The equations of these recursions at the constructors of `ℤ`, and at their successors. The
index `Int.negSucc (k + 1) + 1` reduces to `Int.negSucc k`, and `Int.ofNat k + 1` to
`Int.ofNat (k + 1)`; these lemmas record the resulting unfoldings once, so that the proofs below
rewrite with them instead of relying on the reductions. -/

private theorem liftZ'_ofNat (f : r.Z 0 ⟶ r'.Z 0) (k : ℕ) :
    liftZ' r r' f (Int.ofNat k) = liftPos r r' f k := rfl

private theorem liftZ'_negSucc (f : r.Z 0 ⟶ r'.Z 0) (k : ℕ) :
    liftZ' r r' f (Int.negSucc k) = liftNeg r r' f (k + 1) := rfl

private theorem liftZ'_ofNat_add_one (f : r.Z 0 ⟶ r'.Z 0) (k : ℕ) :
    liftZ' r r' f (Int.ofNat k + 1) = (r.injectivePresentation (Int.ofNat k)).cokernelMap
      (r'.injectivePresentation (Int.ofNat k)) (liftPos r r' f k) := rfl

private theorem liftZ'_negSucc_add_one (f : r.Z 0 ⟶ r'.Z 0) (k : ℕ) :
    liftZ' r r' f (Int.negSucc k + 1) = liftNeg r r' f k := by
  cases k <;> rfl

private theorem liftNeg_succ (f : r.Z 0 ⟶ r'.Z 0) (k : ℕ) :
    liftNeg r r' f (k + 1) = (r.projectivePresentation (Int.negSucc k)).kernelMap
      (r'.projectivePresentation (Int.negSucc k)) (liftNeg r r' f k) := rfl

private theorem liftX_ofNat (f : r.Z 0 ⟶ r'.Z 0) (k : ℕ) :
    liftX r r' f (Int.ofNat k) = (r.injectivePresentation (Int.ofNat k)).middleMap
      (r'.injectivePresentation (Int.ofNat k)) (liftPos r r' f k) := rfl

private theorem liftX_negSucc (f : r.Z 0 ⟶ r'.Z 0) (k : ℕ) :
    liftX r r' f (Int.negSucc k) = (r.projectivePresentation (Int.negSucc k)).middleMap
      (r'.projectivePresentation (Int.negSucc k)) (liftNeg r r' f k) := rfl

/-- The lift on terms extends the lift on cycles. -/
@[reassoc]
private theorem ι_liftX (f : r.Z 0 ⟶ r'.Z 0) (n : ℤ) :
    r.ι n ≫ liftX r r' f n = liftZ' r r' f n ≫ r'.ι n := by
  cases n with
  | ofNat k =>
      rw [liftX_ofNat, liftZ'_ofNat]
      exact (r.injectivePresentation _).i_comp_middleMap _ _
  | negSucc k =>
      rw [liftX_negSucc, liftZ'_negSucc, liftNeg_succ]
      exact ((r.projectivePresentation _).kernelMap_comp_i _ _).symm

/-- The lift on terms induces the lift on cycles in the following degree. -/
@[reassoc]
private theorem liftX_π (f : r.Z 0 ⟶ r'.Z 0) (n : ℤ) :
    liftX r r' f n ≫ r'.π n = r.π n ≫ liftZ' r r' f (n + 1) := by
  cases n with
  | ofNat k =>
      rw [liftX_ofNat, liftZ'_ofNat_add_one]
      exact ((r.injectivePresentation _).p_comp_cokernelMap _ _).symm
  | negSucc k =>
      rw [liftX_negSucc, liftZ'_negSucc_add_one]
      exact (r.projectivePresentation _).middleMap_comp_p _ _

/-- **The comparison map.** The map of complexes lifting `f : r.Z 0 ⟶ r'.Z 0` between the
complexes of two complete resolutions. -/
noncomputable def lift (f : r.Z 0 ⟶ r'.Z 0) : r.complex ⟶ r'.complex where
  f := liftX r r' f
  comm' i j hij := by
    obtain rfl : i + 1 = j := hij
    rw [complex_d, complex_d, d_def, d_def, liftX_π_assoc, Category.assoc, ι_liftX]

/-- The lift induces `f` on the objects of cycles in degree zero. -/
@[reassoc (attr := simp)]
theorem ι_lift_f_zero (f : r.Z 0 ⟶ r'.Z 0) : r.ι 0 ≫ (lift r r' f).f 0 = f ≫ r'.ι 0 :=
  ι_liftX r r' f 0

end Lift

section Homotopy

/-! ### The null-homotopy

Let `φ` lift `f = ι₀ ≫ c ≫ π₋₁`. The null-homotopy has component `c : X⁰ ⟶ X'⁻¹`, and its other
components come from two steps, each stated for an arbitrary degree `n`.

Upwards, a correction `χ : Xⁿ⁺¹ ⟶ X'ⁿ⁺¹` vanishing on `Zⁿ⁺¹`, and agreeing with `φⁿ⁺¹` after the
differential, induces `Zⁿ⁺² ⟶ X'ⁿ⁺¹`. Its extension across `Zⁿ⁺² ↪ Xⁿ⁺²`, into the injective
`X'ⁿ⁺¹`, is a component `h'` with `d ≫ h' = χ`. The next correction is `φⁿ⁺² - h' ≫ d`.

Downwards, a correction `ω : Xⁿ⁺¹ ⟶ X'ⁿ⁺¹` vanishing after `X'ⁿ⁺¹ ↠ Z'ⁿ⁺²`, and agreeing with `φⁿ⁺¹`
before the differential, corestricts to `Xⁿ⁺¹ ⟶ Z'ⁿ⁺¹`; its lift along `X'ⁿ ↠ Z'ⁿ⁺¹`, out of the
projective `Xⁿ⁺¹`, is a component `h'` with `h' ≫ d = ω`. The next correction is `φⁿ - d ≫ h'`.

The corrections in degree zero and `-1` are `φ⁰ - c ≫ d` and `φ⁻¹ - d ≫ c`. -/

variable (φ : r.complex ⟶ r'.complex)

/-- The cancellation behind the upward step: if `d ≫ h' ≫ d = φ ≫ d` in degree `m`, then
`φᵐ⁺¹ - h' ≫ d` vanishes on `Zᵐ⁺¹`, since `Xᵐ ↠ Zᵐ⁺¹` is an epimorphism. -/
private theorem ι_comp_sub_eq_zero_of (m : ℤ) (h' : r.X (m + 1) ⟶ r'.X m)
    (H : r.d m ≫ h' ≫ r'.d m = φ.f m ≫ r'.d m) :
    r.ι (m + 1) ≫ (φ.f (m + 1) - h' ≫ r'.d m) = 0 := by
  rw [← cancel_epi (r.π m), comp_zero, ← Category.assoc, ← d_def, Preadditive.comp_sub,
    ← f_comp_d, H, sub_self]

/-- The cancellation behind the downward step: if `d ≫ h' ≫ d = d ≫ φ` in degree `m`, then
`φᵐ - d ≫ h'` vanishes after `X'ᵐ ↠ Z'ᵐ⁺¹`, since `Z'ᵐ⁺¹ ↪ X'ᵐ⁺¹` is a monomorphism. -/
private theorem sub_comp_π_eq_zero_of (m : ℤ) (h' : r.X (m + 1) ⟶ r'.X m)
    (H : r.d m ≫ h' ≫ r'.d m = r.d m ≫ φ.f (m + 1)) :
    (φ.f m - r.d m ≫ h') ≫ r'.π m = 0 := by
  rw [← cancel_mono (r'.ι (m + 1)), zero_comp, Category.assoc, ← d_def, Preadditive.sub_comp,
    f_comp_d, Category.assoc, H, sub_self]

/-- The upward step of the null-homotopy. -/
private noncomputable def homUp (n : ℤ) (χ : r.X (n + 1) ⟶ r'.X (n + 1))
    (hχ : r.ι (n + 1) ≫ χ = 0) (hχd : χ ≫ r'.d (n + 1) = φ.f (n + 1) ≫ r'.d (n + 1)) :
    { h' : r.X (n + 1 + 1) ⟶ r'.X (n + 1) //
      r.d (n + 1) ≫ h' = χ ∧ r.ι (n + 1 + 1) ≫ (φ.f (n + 1 + 1) - h' ≫ r'.d (n + 1)) = 0 } :=
  let h' := (r'.isInjective_X (n + 1)).factorThru (r.isInflation_ι (n + 1 + 1))
    (r.descZ (n + 1) χ hχ)
  have hd : r.d (n + 1) ≫ h' = χ := by simp [h', d_def]
  ⟨h', hd, ι_comp_sub_eq_zero_of φ (n + 1) h' (by rw [reassoc_of% hd, hχd])⟩

/-- The correction following an upward step agrees with `φ` after the differential. -/
private theorem sub_comp_d_eq (n : ℤ) (h' : r.X (n + 1) ⟶ r'.X n) :
    (φ.f (n + 1) - h' ≫ r'.d n) ≫ r'.d (n + 1) = φ.f (n + 1) ≫ r'.d (n + 1) := by
  rw [Preadditive.sub_comp, Category.assoc, d_d, comp_zero, sub_zero]

/-- The downward step of the null-homotopy. -/
private noncomputable def homDown (n : ℤ) (ω : r.X (n + 1) ⟶ r'.X (n + 1))
    (hω : ω ≫ r'.π (n + 1) = 0) (hdω : r.d n ≫ ω = r.d n ≫ φ.f (n + 1)) :
    { h' : r.X (n + 1) ⟶ r'.X n //
      h' ≫ r'.d n = ω ∧ (φ.f n - r.d n ≫ h') ≫ r'.π n = 0 } :=
  let h' := (r.isProjective_X (n + 1)).factorThru (r'.isDeflation_π n) (r'.liftZ (n + 1) ω hω)
  have hd : h' ≫ r'.d n = ω := by simp [h', d_def]
  ⟨h', hd, sub_comp_π_eq_zero_of φ n h' (by rw [hd, hdω])⟩

/-- The correction following a downward step agrees with `φ` before the differential. -/
private theorem d_comp_sub_eq (n : ℤ) (h' : r.X (n + 1 + 1) ⟶ r'.X (n + 1)) :
    r.d n ≫ (φ.f (n + 1) - r.d (n + 1) ≫ h') = r.d n ≫ φ.f (n + 1) := by
  rw [Preadditive.comp_sub, d_d_assoc, zero_comp, sub_zero]

variable {f : r.Z 0 ⟶ r'.Z 0} (hφ : r.ι 0 ≫ φ.f 0 = f ≫ r'.ι 0)
  (c : r.X 0 ⟶ r'.X (Int.negSucc 0)) (hc : f = r.ι 0 ≫ c ≫ r'.π (Int.negSucc 0))

/-! The two starting corrections, stated in degrees `0` and `-1`. They are the hypotheses of the
first upward step in degree `n = -1` and of the first downward step in degree `n = -2`, whose
indices `Int.negSucc 0 + 1` and `Int.negSucc 1 + 1` reduce to `0` and `Int.negSucc 0`. -/

include hφ hc in
private theorem ι_comp_sub_eq_zero :
    r.ι 0 ≫ (φ.f 0 - c ≫ r'.π (Int.negSucc 0) ≫ r'.ι 0) = 0 := by
  rw [Preadditive.comp_sub, hφ, hc]
  simp

private theorem sub_comp_d_eq_zero :
    (φ.f 0 - c ≫ r'.π (Int.negSucc 0) ≫ r'.ι 0) ≫ r'.d 0 = φ.f 0 ≫ r'.d 0 := by
  rw [Preadditive.sub_comp, d_def]
  simp

include hφ hc in
/-- The start of the downward recursion, from `ι_comp_sub_eq_zero` through
`sub_comp_π_eq_zero_of` in degree `-1`. -/
private theorem sub_comp_π_eq_zero :
    (φ.f (Int.negSucc 0) - r.d (Int.negSucc 0) ≫ c) ≫ r'.π (Int.negSucc 0) = 0 := by
  have h := ι_comp_sub_eq_zero φ hφ c hc
  rw [Preadditive.comp_sub, sub_eq_zero] at h
  have H : r.d (Int.negSucc 0) ≫ c ≫ r'.d (Int.negSucc 0) = r.d (Int.negSucc 0) ≫ φ.f 0 := by
    rw [d_negSucc_zero, d_negSucc_zero, Category.assoc, Category.assoc, h]
  exact sub_comp_π_eq_zero_of φ (Int.negSucc 0) c H

private theorem d_comp_sub_eq_zero :
    r.d (Int.negSucc 1) ≫ (φ.f (Int.negSucc 0) - r.d (Int.negSucc 0) ≫ c) =
      r.d (Int.negSucc 1) ≫ φ.f (Int.negSucc 0) :=
  d_comp_sub_eq φ (Int.negSucc 1) c

/-- The components `Xᵏ⁺¹ ⟶ X'ᵏ` of the null-homotopy in nonnegative degrees, by upward steps from
the correction `φ⁰ - c ≫ d` in degree zero. -/
private noncomputable def homPos : ∀ k : ℕ,
    { h : r.X ((k : ℤ) + 1) ⟶ r'.X k //
      r.ι ((k : ℤ) + 1) ≫ (φ.f ((k : ℤ) + 1) - h ≫ r'.d k) = 0 }
  | 0 =>
      let H := homUp φ (Int.negSucc 0) _ (ι_comp_sub_eq_zero φ hφ c hc) (sub_comp_d_eq_zero φ c)
      ⟨H.1, H.2.2⟩
  | k + 1 =>
      let H := homUp φ k _ (homPos k).2 (sub_comp_d_eq φ k (homPos k).1)
      ⟨H.1, H.2.2⟩

/-- The components `Xⁿ⁺¹ ⟶ X'ⁿ` of the null-homotopy in degrees `n = Int.negSucc (k + 1)`, by
downward steps from the correction `φ⁻¹ - d ≫ c` in degree `-1`. -/
private noncomputable def homNeg : ∀ k : ℕ,
    { h : r.X (Int.negSucc (k + 1) + 1) ⟶ r'.X (Int.negSucc (k + 1)) //
      (φ.f (Int.negSucc (k + 1)) - r.d (Int.negSucc (k + 1)) ≫ h) ≫
        r'.π (Int.negSucc (k + 1)) = 0 }
  | 0 =>
      let H := homDown φ (Int.negSucc 1) _ (sub_comp_π_eq_zero φ hφ c hc) (d_comp_sub_eq_zero φ c)
      ⟨H.1, H.2.2⟩
  | k + 1 =>
      let H := homDown φ (Int.negSucc (k + 2)) _ (homNeg k).2
        (d_comp_sub_eq φ (Int.negSucc (k + 2)) (homNeg k).1)
      ⟨H.1, H.2.2⟩

/-- The components `Xⁿ⁺¹ ⟶ X'ⁿ` of the null-homotopy. -/
private noncomputable def homotopyHom : ∀ n : ℤ, r.X (n + 1) ⟶ r'.X n
  | Int.ofNat k => (homPos φ hφ c hc k).1
  | Int.negSucc 0 => c
  | Int.negSucc (k + 1) => (homNeg φ hφ c hc k).1

/-! The equations of these recursions at the constructors of `ℤ` and at their successors, by
`rfl`, as for the lift. -/

private theorem homPos_zero :
    (homPos φ hφ c hc 0).1 =
      (homUp φ (Int.negSucc 0) _ (ι_comp_sub_eq_zero φ hφ c hc) (sub_comp_d_eq_zero φ c)).1 :=
  rfl

private theorem homPos_succ (k : ℕ) :
    (homPos φ hφ c hc (k + 1)).1 = (homUp φ k _ (homPos φ hφ c hc k).2
      (sub_comp_d_eq φ k (homPos φ hφ c hc k).1)).1 :=
  rfl

private theorem homNeg_zero :
    (homNeg φ hφ c hc 0).1 =
      (homDown φ (Int.negSucc 1) _ (sub_comp_π_eq_zero φ hφ c hc) (d_comp_sub_eq_zero φ c)).1 :=
  rfl

private theorem homNeg_succ (k : ℕ) :
    (homNeg φ hφ c hc (k + 1)).1 = (homDown φ (Int.negSucc (k + 2)) _ (homNeg φ hφ c hc k).2
      (d_comp_sub_eq φ (Int.negSucc (k + 2)) (homNeg φ hφ c hc k).1)).1 :=
  rfl

private theorem homotopyHom_ofNat (k : ℕ) :
    homotopyHom φ hφ c hc (Int.ofNat k) = (homPos φ hφ c hc k).1 := rfl

private theorem homotopyHom_ofNat_add_one (k : ℕ) :
    homotopyHom φ hφ c hc (Int.ofNat k + 1) = (homPos φ hφ c hc (k + 1)).1 := rfl

private theorem homotopyHom_negSucc_zero : homotopyHom φ hφ c hc (Int.negSucc 0) = c := rfl

private theorem homotopyHom_negSucc_zero_add_one :
    homotopyHom φ hφ c hc (Int.negSucc 0 + 1) = (homPos φ hφ c hc 0).1 := rfl

private theorem homotopyHom_negSucc_succ (k : ℕ) :
    homotopyHom φ hφ c hc (Int.negSucc (k + 1)) = (homNeg φ hφ c hc k).1 := rfl

private theorem homotopyHom_negSucc_one_add_one :
    homotopyHom φ hφ c hc (Int.negSucc 1 + 1) = c := rfl

private theorem homotopyHom_negSucc_add_two_add_one (k : ℕ) :
    homotopyHom φ hφ c hc (Int.negSucc (k + 2) + 1) = (homNeg φ hφ c hc k).1 := rfl

/-! The homotopy identities, one for each kind of degree: each is the equation `d ≫ h' = χ` or
`h' ≫ d = ω` returned by the step that produced the component. After the equations above, the
goal and that equation differ only in the indices `Int.ofNat k + 1` against `↑k + 1` and
`Int.negSucc (k + 1) + 1` against `Int.negSucc k`, which `exact` identifies by reduction. -/

private theorem comm_ofNat (k : ℕ) :
    φ.f (Int.ofNat k + 1) = r.d (Int.ofNat k + 1) ≫ homotopyHom φ hφ c hc (Int.ofNat k + 1) +
      homotopyHom φ hφ c hc (Int.ofNat k) ≫ r'.d (Int.ofNat k) := by
  rw [← sub_eq_iff_eq_add, homotopyHom_ofNat_add_one, homotopyHom_ofNat, homPos_succ]
  exact (homUp φ k _ (homPos φ hφ c hc k).2 (sub_comp_d_eq φ k (homPos φ hφ c hc k).1)).2.1.symm

private theorem comm_negSucc_zero :
    φ.f (Int.negSucc 0 + 1) =
      r.d (Int.negSucc 0 + 1) ≫ homotopyHom φ hφ c hc (Int.negSucc 0 + 1) +
        homotopyHom φ hφ c hc (Int.negSucc 0) ≫ r'.d (Int.negSucc 0) := by
  rw [← sub_eq_iff_eq_add, d_negSucc_zero, homotopyHom_negSucc_zero_add_one,
    homotopyHom_negSucc_zero, homPos_zero]
  exact (homUp φ (Int.negSucc 0) _ (ι_comp_sub_eq_zero φ hφ c hc)
    (sub_comp_d_eq_zero φ c)).2.1.symm

private theorem comm_negSucc_one :
    φ.f (Int.negSucc 1 + 1) =
      r.d (Int.negSucc 1 + 1) ≫ homotopyHom φ hφ c hc (Int.negSucc 1 + 1) +
        homotopyHom φ hφ c hc (Int.negSucc 1) ≫ r'.d (Int.negSucc 1) := by
  rw [← sub_eq_iff_eq_add', homotopyHom_negSucc_one_add_one, homotopyHom_negSucc_succ, homNeg_zero]
  exact (homDown φ (Int.negSucc 1) _ (sub_comp_π_eq_zero φ hφ c hc)
    (d_comp_sub_eq_zero φ c)).2.1.symm

private theorem comm_negSucc_add_two (k : ℕ) :
    φ.f (Int.negSucc (k + 2) + 1) =
      r.d (Int.negSucc (k + 2) + 1) ≫ homotopyHom φ hφ c hc (Int.negSucc (k + 2) + 1) +
        homotopyHom φ hφ c hc (Int.negSucc (k + 2)) ≫ r'.d (Int.negSucc (k + 2)) := by
  rw [← sub_eq_iff_eq_add', homotopyHom_negSucc_add_two_add_one, homotopyHom_negSucc_succ,
    homNeg_succ]
  exact (homDown φ (Int.negSucc (k + 2)) _ (homNeg φ hφ c hc k).2
    (d_comp_sub_eq φ (Int.negSucc (k + 2)) (homNeg φ hφ c hc k).1)).2.1.symm

/-- The null-homotopy of a map of complexes lifting `f = ι₀ ≫ c ≫ π₋₁`. -/
private noncomputable def homotopyZeroOfEq : Homotopy φ 0 :=
  Homotopy.mkCochainComplexInt φ (homotopyHom φ hφ c hc) fun n => by
    rw [complex_d, complex_d]
    match n with
    | Int.ofNat k => exact comm_ofNat φ hφ c hc k
    | Int.negSucc 0 => exact comm_negSucc_zero φ hφ c hc
    | Int.negSucc 1 => exact comm_negSucc_one φ hφ c hc
    | Int.negSucc (k + 2) => exact comm_negSucc_add_two φ hφ c hc k

variable {φ}

/-- A morphism of the objects of cycles in degree zero factoring through a projective-injective
object factors as `ι₀ ≫ c ≫ π₋₁`, through the inflation `Z⁰ ↪ X⁰` and the deflation
`X'⁻¹ ↠ Z'⁰`. -/
private theorem exists_eq_ι_comp_comp_π (hf : E.projectiveInjective.FactorsThrough f) :
    ∃ c : r.X 0 ⟶ r'.X (Int.negSucc 0), f = r.ι 0 ≫ c ≫ r'.π (Int.negSucc 0) := by
  obtain ⟨Q, hQ, a, b, rfl⟩ := (ObjectProperty.factorsThrough_iff _ _).mp hf
  rw [E.projectiveInjective_iff] at hQ
  exact ⟨hQ.2.factorThru (r.isInflation_ι 0) a ≫
      hQ.1.factorThru (r'.isDeflation_π (Int.negSucc 0)) b, by simp⟩

/-- **The homotopy criterion.** A map of complexes lifting a morphism that factors through a
projective-injective object is null-homotopic. -/
noncomputable def liftHomotopyZero (φ : r.complex ⟶ r'.complex)
    (hφ : r.ι 0 ≫ φ.f 0 = f ≫ r'.ι 0) (hf : E.projectiveInjective.FactorsThrough f) :
    Homotopy φ 0 :=
  homotopyZeroOfEq φ hφ (exists_eq_ι_comp_comp_π hf).choose
    (exists_eq_ι_comp_comp_π hf).choose_spec

/-- Conversely, if a map of complexes lifting `f` is null-homotopic, then `f` factors through
the projective-injective term `X⁰`. -/
theorem factorsThrough_of_homotopy (hφ : r.ι 0 ≫ φ.f 0 = f ≫ r'.ι 0) (h : Homotopy φ 0) :
    E.projectiveInjective.FactorsThrough f := by
  have hcomm := h.comm 0
  rw [dNext_eq _ (ComplexShape.up_mk 0 (0 + 1) rfl),
    prevD_eq _ (ComplexShape.up_mk (Int.negSucc 0) 0 rfl),
    complex_d, complex_d_negSucc_zero] at hcomm
  have : f = r.ι 0 ≫ h.hom 0 (Int.negSucc 0) ≫ r'.π (Int.negSucc 0) := by
    rw [← cancel_mono (r'.ι 0), ← hφ, hcomm]
    simp [d_def]
  rw [this]
  exact ObjectProperty.factorsThrough_comp _ (r.projectiveInjective 0) (r.ι 0) _

/-- A map of complexes lifting `f` is null-homotopic if and only if `f` factors through a
projective-injective object. When `E` is Frobenius, this says that `f` vanishes in the stable
category, by `TauCeti.ExactStructure.IsFrobenius.projectiveInjective_eq_isProjective` and
`TauCeti.ExactStructure.projectiveStableFunctor_map_eq_zero_iff`. -/
theorem nonempty_homotopy_zero_iff (hφ : r.ι 0 ≫ φ.f 0 = f ≫ r'.ι 0) :
    Nonempty (Homotopy φ 0) ↔ E.projectiveInjective.FactorsThrough f :=
  ⟨fun ⟨h⟩ => factorsThrough_of_homotopy hφ h, fun hf => ⟨liftHomotopyZero φ hφ hf⟩⟩

/-- Two lifts of the same morphism are homotopic. -/
noncomputable def liftHomotopy (f : r.Z 0 ⟶ r'.Z 0) (φ ψ : r.complex ⟶ r'.complex)
    (hφ : r.ι 0 ≫ φ.f 0 = f ≫ r'.ι 0) (hψ : r.ι 0 ≫ ψ.f 0 = f ≫ r'.ι 0) : Homotopy φ ψ :=
  Homotopy.equivSubZero.symm (liftHomotopyZero (f := 0) (φ - ψ)
    (by simp [Preadditive.comp_sub, hφ, hψ]) (ObjectProperty.FactorsThrough.zero _ _ _))

variable (r r')

/-- The lift of the identity is homotopic to the identity. -/
noncomputable def liftIdHomotopy : Homotopy (lift r r (𝟙 (r.Z 0))) (𝟙 r.complex) :=
  liftHomotopy (𝟙 _) _ _ (by simp) (by simp)

/-- The lift of a composite is homotopic to the composite of the lifts. -/
noncomputable def liftCompHomotopy (r'' : E.CompleteResolution) (f : r.Z 0 ⟶ r'.Z 0)
    (g : r'.Z 0 ⟶ r''.Z 0) : Homotopy (lift r r'' (f ≫ g)) (lift r r' f ≫ lift r' r'' g) :=
  liftHomotopy (f ≫ g) _ _ (by simp) (by simp)

/-- **Uniqueness of complete resolutions up to homotopy.** Complete resolutions whose objects of
cycles in degree zero are isomorphic have homotopy equivalent complexes. -/
noncomputable def homotopyEquiv (e : r.Z 0 ≅ r'.Z 0) : HomotopyEquiv r.complex r'.complex where
  hom := lift r r' e.hom
  inv := lift r' r e.inv
  homotopyHomInvId := liftHomotopy (𝟙 _) _ _ (by simp) (by simp)
  homotopyInvHomId := liftHomotopy (𝟙 _) _ _ (by simp) (by simp)

/-- The homotopy equivalence induces `e.hom` on the objects of cycles in degree zero. -/
@[reassoc (attr := simp)]
theorem ι_homotopyEquiv_hom_f_zero (e : r.Z 0 ≅ r'.Z 0) :
    r.ι 0 ≫ (homotopyEquiv r r' e).hom.f 0 = e.hom ≫ r'.ι 0 :=
  ι_lift_f_zero r r' e.hom

/-- The homotopy equivalence induces `e.inv` on the objects of cycles in degree zero. -/
@[reassoc (attr := simp)]
theorem ι_homotopyEquiv_inv_f_zero (e : r.Z 0 ≅ r'.Z 0) :
    r'.ι 0 ≫ (homotopyEquiv r r' e).inv.f 0 = e.inv ≫ r.ι 0 :=
  ι_lift_f_zero r' r e.inv

end Homotopy

end CompleteResolution

end ExactStructure

end TauCeti
