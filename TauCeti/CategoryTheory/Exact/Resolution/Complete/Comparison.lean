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
projective-injective object, that is, when `f` vanishes in the stable category. In particular two
lifts of the same morphism are homotopic, and two complete resolutions with isomorphic objects of
cycles in degree zero are homotopy equivalent. In a Frobenius exact category every object has a
complete resolution, so complete resolutions are unique up to homotopy equivalence.

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
-/

public section

namespace TauCeti

open CategoryTheory CategoryTheory.Limits

universe v u

variable {C : Type u} [Category.{v} C] [Preadditive C] [HasZeroObject C] [HasBinaryBiproducts C]

namespace ExactStructure

namespace CompleteResolution

variable {E : ExactStructure C} (r r' : E.CompleteResolution)

section Lift

/-- The components on cycles of the lift in nonnegative degrees: `f` in degree zero, and in
degree `k + 1` the morphism induced on cokernels by the component on terms in degree `k`. -/
private noncomputable def liftPos (f : r.Z 0 ⟶ r'.Z 0) : ∀ k : ℕ, r.Z k ⟶ r'.Z k
  | 0 => f
  | k + 1 =>
      r.descZ k ((r'.isInjective_X k).factorThru (r.isInflation_ι k) (liftPos f k ≫ r'.ι k) ≫
        r'.π k) (by simp)

/-- The component on terms of the lift in degree `k ≥ 0`: an extension of the component on cycles
across the inflation `Zᵏ ↪ Xᵏ`, into the injective term of `r'`. -/
private noncomputable def liftPosX (f : r.Z 0 ⟶ r'.Z 0) (k : ℕ) : r.X k ⟶ r'.X k :=
  (r'.isInjective_X k).factorThru (r.isInflation_ι k) (liftPos r r' f k ≫ r'.ι k)

@[reassoc]
private theorem ι_liftPosX (f : r.Z 0 ⟶ r'.Z 0) (k : ℕ) :
    r.ι k ≫ liftPosX r r' f k = liftPos r r' f k ≫ r'.ι k := by
  simp [liftPosX]

@[reassoc]
private theorem π_liftPos (f : r.Z 0 ⟶ r'.Z 0) (k : ℕ) :
    r.π k ≫ liftPos r r' f (k + 1) = liftPosX r r' f k ≫ r'.π k := by
  simp [liftPos, liftPosX]

/-- The components on cycles of the lift in nonpositive degrees, indexed so that `liftNeg f k`
is the component in degree `Int.negSucc k + 1`: `f` in degree zero, and in degree
`Int.negSucc k` the morphism induced on kernels by the component on terms there. -/
private noncomputable def liftNeg (f : r.Z 0 ⟶ r'.Z 0) :
    ∀ k : ℕ, r.Z (Int.negSucc k + 1) ⟶ r'.Z (Int.negSucc k + 1)
  | 0 => f
  | k + 1 =>
      r'.liftZ (Int.negSucc k) (r.ι (Int.negSucc k) ≫
        (r.isProjective_X (Int.negSucc k)).factorThru (r'.isDeflation_π (Int.negSucc k))
          (r.π (Int.negSucc k) ≫ liftNeg f k)) (by simp)

/-- The component on terms of the lift in degree `Int.negSucc k`: a lift of the component on
cycles along the deflation `X'ⁿ ↠ Z'ⁿ⁺¹`, out of the projective term of `r`. -/
private noncomputable def liftNegX (f : r.Z 0 ⟶ r'.Z 0) (k : ℕ) :
    r.X (Int.negSucc k) ⟶ r'.X (Int.negSucc k) :=
  (r.isProjective_X (Int.negSucc k)).factorThru (r'.isDeflation_π (Int.negSucc k))
    (r.π (Int.negSucc k) ≫ liftNeg r r' f k)

@[reassoc]
private theorem liftNegX_π (f : r.Z 0 ⟶ r'.Z 0) (k : ℕ) :
    liftNegX r r' f k ≫ r'.π (Int.negSucc k) = r.π (Int.negSucc k) ≫ liftNeg r r' f k := by
  simp [liftNegX]

@[reassoc]
private theorem liftNeg_ι (f : r.Z 0 ⟶ r'.Z 0) (k : ℕ) :
    liftNeg r r' f (k + 1) ≫ r'.ι (Int.negSucc k) = r.ι (Int.negSucc k) ≫ liftNegX r r' f k := by
  simp [liftNeg, liftNegX]

/-- The components on terms of the lift. -/
private noncomputable def liftX (f : r.Z 0 ⟶ r'.Z 0) : ∀ n : ℤ, r.X n ⟶ r'.X n
  | Int.ofNat k => liftPosX r r' f k
  | Int.negSucc k => liftNegX r r' f k

private theorem liftX_comm (f : r.Z 0 ⟶ r'.Z 0) (n : ℤ) :
    liftX r r' f n ≫ r'.d n = r.d n ≫ liftX r r' f (n + 1) := by
  simp only [d_def]
  -- In each case `change` unfolds `liftX` at a constructor. It also writes the indices
  -- `Int.ofNat k + 1` and `Int.negSucc (k + 1) + 1` as `↑(k + 1)` and `Int.negSucc k`: these
  -- agree definitionally, but only the latter forms match the lemmas.
  match n with
  | Int.ofNat k =>
      change liftPosX r r' f k ≫ r'.π k ≫ r'.ι ((k + 1 : ℕ) : ℤ) =
        (r.π k ≫ r.ι ((k + 1 : ℕ) : ℤ)) ≫ liftPosX r r' f (k + 1)
      rw [Category.assoc, ι_liftPosX, π_liftPos_assoc]
  | Int.negSucc 0 =>
      change liftNegX r r' f 0 ≫ r'.π (Int.negSucc 0) ≫ r'.ι ((0 : ℕ) : ℤ) =
        (r.π (Int.negSucc 0) ≫ r.ι ((0 : ℕ) : ℤ)) ≫ liftPosX r r' f 0
      rw [Category.assoc, ι_liftPosX, liftNegX_π_assoc]
      rfl
  | Int.negSucc (k + 1) =>
      change liftNegX r r' f (k + 1) ≫ r'.π (Int.negSucc (k + 1)) ≫ r'.ι (Int.negSucc k) =
        (r.π (Int.negSucc (k + 1)) ≫ r.ι (Int.negSucc k)) ≫ liftNegX r r' f k
      rw [liftNegX_π_assoc, Category.assoc, ← liftNeg_ι]

/-- **The comparison map.** The map of complexes lifting `f : r.Z 0 ⟶ r'.Z 0` between the
complexes of two complete resolutions. -/
noncomputable def lift (f : r.Z 0 ⟶ r'.Z 0) : r.complex ⟶ r'.complex where
  f := liftX r r' f
  comm' i j hij := by
    obtain rfl : i + 1 = j := hij
    rw [complex_d, complex_d]
    exact liftX_comm r r' f i

/-- The lift induces `f` on the objects of cycles in degree zero. -/
@[reassoc (attr := simp)]
theorem ι_lift_f_zero (f : r.Z 0 ⟶ r'.Z 0) : r.ι 0 ≫ (lift r r' f).f 0 = f ≫ r'.ι 0 :=
  ι_liftPosX r r' f 0

end Lift

section Homotopy

variable {r r'}

/-- The commutation of a map of complexes with the differentials, in terms of the differentials
of the complete resolutions. -/
private theorem comm_d (φ : r.complex ⟶ r'.complex) (n : ℤ) :
    φ.f n ≫ r'.d n = r.d n ≫ φ.f (n + 1) := by
  rw [← complex_d, ← complex_d]
  exact φ.comm n (n + 1)


/-- The corrections of `φ` in nonnegative degrees. In degree `k` the correction is
`φᵏ - hᵏ ≫ d`, where `h⁰ = c` and `hᵏ` is the component of the null-homotopy constructed in the
previous step. It vanishes on `Zᵏ`, and agrees with `φᵏ` after the differential. -/
private noncomputable def homPos (φ : r.complex ⟶ r'.complex) {f : r.Z 0 ⟶ r'.Z 0}
    (hφ : r.ι 0 ≫ φ.f 0 = f ≫ r'.ι 0) (c : r.X 0 ⟶ r'.X (Int.negSucc 0))
    (hc : f = r.ι 0 ≫ c ≫ r'.π (Int.negSucc 0)) : ∀ k : ℕ,
    { χ : r.X k ⟶ r'.X k // r.ι k ≫ χ = 0 ∧ χ ≫ r'.d k = φ.f k ≫ r'.d k }
  | 0 => ⟨φ.f 0 - c ≫ r'.complex.d (Int.negSucc 0) 0, by
      constructor
      -- `change` writes the index `↑(0 : ℕ)` of the subtype as `0`, the index of `hφ` and `hc`.
      · change r.ι 0 ≫ (φ.f 0 - c ≫ r'.complex.d (Int.negSucc 0) 0) = 0
        rw [complex_d_negSucc_zero, Preadditive.comp_sub, hφ, hc, d_def]
        simp only [Category.assoc]
        exact sub_self _
      · change (φ.f 0 - c ≫ r'.complex.d (Int.negSucc 0) 0) ≫ r'.d 0 = φ.f 0 ≫ r'.d 0
        rw [complex_d_negSucc_zero, Preadditive.sub_comp, Category.assoc,
          show r'.d (Int.negSucc 0) ≫ r'.d 0 = 0 from r'.d_d _, comp_zero, sub_zero]⟩
  | k + 1 =>
      let χ := homPos φ hφ c hc k
      let h := (r'.isInjective_X k).factorThru (r.isInflation_ι ((k : ℤ) + 1))
        (r.descZ k χ.1 χ.2.1)
      have hd : r.d k ≫ h = χ.1 := by simp [h, d_def]
      -- `show` gives `h ≫ r'.d k`, of type `r.X (↑k + 1) ⟶ r'.X (↑k + 1)`, the type
      -- `r.X ↑(k + 1) ⟶ r'.X ↑(k + 1)` of `φ.f ↑(k + 1)`; the indices agree definitionally.
      ⟨φ.f ((k + 1 : ℕ) : ℤ) -
          show r.X ((k + 1 : ℕ) : ℤ) ⟶ r'.X ((k + 1 : ℕ) : ℤ) from h ≫ r'.d k, by
        constructor
        · rw [← cancel_epi (r.π k), comp_zero, ← Category.assoc]
          -- `change` writes `↑(k + 1)` as `↑k + 1`, the index of `d_def` and `comm_d`.
          change (r.π k ≫ r.ι ((k : ℤ) + 1)) ≫ (φ.f ((k : ℤ) + 1) - h ≫ r'.d k) = 0
          rw [← d_def, Preadditive.comp_sub, ← comm_d, reassoc_of% hd, χ.2.2, sub_self]
        · change (φ.f ((k : ℤ) + 1) - h ≫ r'.d k) ≫ r'.d ((k : ℤ) + 1) =
            φ.f ((k : ℤ) + 1) ≫ r'.d ((k : ℤ) + 1)
          rw [Preadditive.sub_comp, Category.assoc, d_d, comp_zero, sub_zero]⟩

/-- The component `hᵏ⁺¹ : Xᵏ⁺¹ ⟶ X'ᵏ` of the null-homotopy in nonnegative degrees: an extension
across `Zᵏ⁺¹ ↪ Xᵏ⁺¹`, into the injective term `X'ᵏ`, of the morphism induced on `Zᵏ⁺¹` by the
correction in degree `k`. -/
private noncomputable def hPos (φ : r.complex ⟶ r'.complex) {f : r.Z 0 ⟶ r'.Z 0}
    (hφ : r.ι 0 ≫ φ.f 0 = f ≫ r'.ι 0) (c : r.X 0 ⟶ r'.X (Int.negSucc 0))
    (hc : f = r.ι 0 ≫ c ≫ r'.π (Int.negSucc 0)) (k : ℕ) : r.X ((k : ℤ) + 1) ⟶ r'.X k :=
  (r'.isInjective_X k).factorThru (r.isInflation_ι ((k : ℤ) + 1))
    (r.descZ k (homPos φ hφ c hc k).1 (homPos φ hφ c hc k).2.1)

private theorem d_hPos (φ : r.complex ⟶ r'.complex) {f : r.Z 0 ⟶ r'.Z 0}
    (hφ : r.ι 0 ≫ φ.f 0 = f ≫ r'.ι 0) (c : r.X 0 ⟶ r'.X (Int.negSucc 0))
    (hc : f = r.ι 0 ≫ c ≫ r'.π (Int.negSucc 0)) (k : ℕ) :
    r.d k ≫ hPos φ hφ c hc k = (homPos φ hφ c hc k).1 := by
  simp [hPos, d_def]

private theorem homPos_succ (φ : r.complex ⟶ r'.complex) {f : r.Z 0 ⟶ r'.Z 0}
    (hφ : r.ι 0 ≫ φ.f 0 = f ≫ r'.ι 0) (c : r.X 0 ⟶ r'.X (Int.negSucc 0))
    (hc : f = r.ι 0 ≫ c ≫ r'.π (Int.negSucc 0)) (k : ℕ) :
    (homPos φ hφ c hc (k + 1)).1 = φ.f ((k : ℤ) + 1) - hPos φ hφ c hc k ≫ r'.d k :=
  rfl

private theorem homPos_zero (φ : r.complex ⟶ r'.complex) {f : r.Z 0 ⟶ r'.Z 0}
    (hφ : r.ι 0 ≫ φ.f 0 = f ≫ r'.ι 0) (c : r.X 0 ⟶ r'.X (Int.negSucc 0))
    (hc : f = r.ι 0 ≫ c ≫ r'.π (Int.negSucc 0)) :
    (homPos φ hφ c hc 0).1 = φ.f 0 - c ≫ r'.complex.d (Int.negSucc 0) 0 :=
  rfl

/-- The corrections of `φ` in negative degrees. In degree `Int.negSucc k` the correction is
`φ - d ≫ h`, where the component `h` out of the following degree is `c` for `k = 0` and was
constructed in the previous step otherwise. It vanishes after `X'ⁿ ↠ Z'ⁿ⁺¹`, and agrees with `φ`
before the differential. -/
private noncomputable def homNeg (φ : r.complex ⟶ r'.complex) {f : r.Z 0 ⟶ r'.Z 0}
    (hφ : r.ι 0 ≫ φ.f 0 = f ≫ r'.ι 0) (c : r.X 0 ⟶ r'.X (Int.negSucc 0))
    (hc : f = r.ι 0 ≫ c ≫ r'.π (Int.negSucc 0)) : ∀ k : ℕ,
    { ω : r.X (Int.negSucc k) ⟶ r'.X (Int.negSucc k) // ω ≫ r'.π (Int.negSucc k) = 0 ∧
      r.d (Int.negSucc (k + 1)) ≫ ω = r.d (Int.negSucc (k + 1)) ≫ φ.f (Int.negSucc k) }
  | 0 => ⟨φ.f (Int.negSucc 0) - r.d (Int.negSucc 0) ≫ c, by
      constructor
      · rw [← cancel_mono (r'.ι 0), zero_comp, Category.assoc]
        -- `change` writes the index `0` of `ι` as `Int.negSucc 0 + 1`, the index of `d_def`.
        change (φ.f (Int.negSucc 0) - r.d (Int.negSucc 0) ≫ c) ≫
          r'.π (Int.negSucc 0) ≫ r'.ι (Int.negSucc 0 + 1) = 0
        rw [← d_def, Preadditive.sub_comp, comm_d]
        simp only [d_def]
        -- `change` writes `Int.negSucc 0 + 1` as `0`, the index of `hφ`.
        change (r.π (Int.negSucc 0) ≫ r.ι 0) ≫ φ.f 0 -
          ((r.π (Int.negSucc 0) ≫ r.ι 0) ≫ c) ≫ r'.π (Int.negSucc 0) ≫ r'.ι 0 = 0
        simp only [Category.assoc, hφ]
        rw [hc]
        simp only [Category.assoc]
        exact sub_self _
      · rw [Preadditive.comp_sub, ← Category.assoc,
          show r.d (Int.negSucc (0 + 1)) ≫ r.d (Int.negSucc 0) = 0 from r.d_d _, zero_comp,
          sub_zero]⟩
  | k + 1 =>
      let ω := homNeg φ hφ c hc k
      let h := (r.isProjective_X (Int.negSucc k)).factorThru
        (r'.isDeflation_π (Int.negSucc (k + 1))) (r'.liftZ (Int.negSucc k) ω.1 ω.2.1)
      have hd : h ≫ r'.d (Int.negSucc (k + 1)) = ω.1 := by
        rw [d_def]
        -- `change` writes `Int.negSucc (k + 1) + 1` as `Int.negSucc k`, the index of `liftZ_ι`.
        change h ≫ r'.π (Int.negSucc (k + 1)) ≫ r'.ι (Int.negSucc k) = ω.1
        rw [isProjective.factorThru_comp_assoc]
        exact r'.liftZ_ι _ _ _
      ⟨φ.f (Int.negSucc (k + 1)) - r.d (Int.negSucc (k + 1)) ≫ h, by
        constructor
        · rw [← cancel_mono (r'.ι (Int.negSucc k)), zero_comp, Category.assoc]
          -- `change` writes `Int.negSucc k` as `Int.negSucc (k + 1) + 1`, the index of `d_def`.
          change (φ.f (Int.negSucc (k + 1)) - r.d (Int.negSucc (k + 1)) ≫ h) ≫
            r'.π (Int.negSucc (k + 1)) ≫ r'.ι (Int.negSucc (k + 1) + 1) = 0
          rw [← d_def, Preadditive.sub_comp, comm_d, Category.assoc, hd, ω.2.2]
          exact sub_self _
        · rw [Preadditive.comp_sub, ← Category.assoc,
            show r.d (Int.negSucc (k + 1 + 1)) ≫ r.d (Int.negSucc (k + 1)) = 0 from r.d_d _,
            zero_comp, sub_zero]⟩

/-- The component `X'ⁿ⁺¹ ⟶ X'ⁿ` of the null-homotopy out of degree `Int.negSucc k`, into degree
`Int.negSucc (k + 1)`: a lift along `X'ⁿ ↠ Z'ⁿ⁺¹`, out of the projective term, of the morphism
into `Z'ⁿ⁺¹` induced by the correction in degree `Int.negSucc k`. -/
private noncomputable def hNeg (φ : r.complex ⟶ r'.complex) {f : r.Z 0 ⟶ r'.Z 0}
    (hφ : r.ι 0 ≫ φ.f 0 = f ≫ r'.ι 0) (c : r.X 0 ⟶ r'.X (Int.negSucc 0))
    (hc : f = r.ι 0 ≫ c ≫ r'.π (Int.negSucc 0)) (k : ℕ) :
    r.X (Int.negSucc k) ⟶ r'.X (Int.negSucc (k + 1)) :=
  (r.isProjective_X (Int.negSucc k)).factorThru (r'.isDeflation_π (Int.negSucc (k + 1)))
    (r'.liftZ (Int.negSucc k) (homNeg φ hφ c hc k).1 (homNeg φ hφ c hc k).2.1)

private theorem hNeg_d (φ : r.complex ⟶ r'.complex) {f : r.Z 0 ⟶ r'.Z 0}
    (hφ : r.ι 0 ≫ φ.f 0 = f ≫ r'.ι 0) (c : r.X 0 ⟶ r'.X (Int.negSucc 0))
    (hc : f = r.ι 0 ≫ c ≫ r'.π (Int.negSucc 0)) (k : ℕ) :
    hNeg φ hφ c hc k ≫ r'.d (Int.negSucc (k + 1)) = (homNeg φ hφ c hc k).1 := by
  rw [d_def]
  -- `change` writes `Int.negSucc (k + 1) + 1` as `Int.negSucc k`, the index of `liftZ_ι`.
  change hNeg φ hφ c hc k ≫ r'.π (Int.negSucc (k + 1)) ≫ r'.ι (Int.negSucc k) = _
  rw [hNeg, isProjective.factorThru_comp_assoc]
  exact r'.liftZ_ι _ _ _

private theorem homNeg_succ (φ : r.complex ⟶ r'.complex) {f : r.Z 0 ⟶ r'.Z 0}
    (hφ : r.ι 0 ≫ φ.f 0 = f ≫ r'.ι 0) (c : r.X 0 ⟶ r'.X (Int.negSucc 0))
    (hc : f = r.ι 0 ≫ c ≫ r'.π (Int.negSucc 0)) (k : ℕ) :
    (homNeg φ hφ c hc (k + 1)).1 =
      φ.f (Int.negSucc (k + 1)) - r.d (Int.negSucc (k + 1)) ≫ hNeg φ hφ c hc k :=
  rfl

private theorem homNeg_zero (φ : r.complex ⟶ r'.complex) {f : r.Z 0 ⟶ r'.Z 0}
    (hφ : r.ι 0 ≫ φ.f 0 = f ≫ r'.ι 0) (c : r.X 0 ⟶ r'.X (Int.negSucc 0))
    (hc : f = r.ι 0 ≫ c ≫ r'.π (Int.negSucc 0)) :
    (homNeg φ hφ c hc 0).1 = φ.f (Int.negSucc 0) - r.d (Int.negSucc 0) ≫ c :=
  rfl

/-- The components `Xⁿ⁺¹ ⟶ X'ⁿ` of the null-homotopy: `c` out of degree zero, and the
components constructed in nonnegative and negative degrees otherwise. -/
private noncomputable def homotopyHom (φ : r.complex ⟶ r'.complex) {f : r.Z 0 ⟶ r'.Z 0}
    (hφ : r.ι 0 ≫ φ.f 0 = f ≫ r'.ι 0) (c : r.X 0 ⟶ r'.X (Int.negSucc 0))
    (hc : f = r.ι 0 ≫ c ≫ r'.π (Int.negSucc 0)) : ∀ n : ℤ, r.X (n + 1) ⟶ r'.X n
  | Int.ofNat k => hPos φ hφ c hc k
  | Int.negSucc 0 => c
  | Int.negSucc (k + 1) => hNeg φ hφ c hc k

private theorem homotopyHom_comm (φ : r.complex ⟶ r'.complex) {f : r.Z 0 ⟶ r'.Z 0}
    (hφ : r.ι 0 ≫ φ.f 0 = f ≫ r'.ι 0) (c : r.X 0 ⟶ r'.X (Int.negSucc 0))
    (hc : f = r.ι 0 ≫ c ≫ r'.π (Int.negSucc 0)) (n : ℤ) :
    φ.f (n + 1) = r.d (n + 1) ≫ homotopyHom φ hφ c hc (n + 1) +
      homotopyHom φ hφ c hc n ≫ r'.d n := by
  match n with
  | Int.ofNat k =>
      rw [← sub_eq_iff_eq_add]
      exact (homPos_succ φ hφ c hc k).symm.trans (d_hPos φ hφ c hc (k + 1)).symm
  | Int.negSucc 0 =>
      rw [← sub_eq_iff_eq_add, ← complex_d_negSucc_zero]
      exact (homPos_zero φ hφ c hc).symm.trans (d_hPos φ hφ c hc 0).symm
  | Int.negSucc 1 =>
      rw [← sub_eq_iff_eq_add']
      exact (homNeg_zero φ hφ c hc).symm.trans (hNeg_d φ hφ c hc 0).symm
  | Int.negSucc (k + 2) =>
      rw [← sub_eq_iff_eq_add']
      exact (homNeg_succ φ hφ c hc k).symm.trans (hNeg_d φ hφ c hc (k + 1)).symm

/-- The null-homotopy of a map of complexes lifting `f = ι₀ ≫ c ≫ π₋₁`. -/
private noncomputable def homotopyZeroOfEq (φ : r.complex ⟶ r'.complex) {f : r.Z 0 ⟶ r'.Z 0}
    (hφ : r.ι 0 ≫ φ.f 0 = f ≫ r'.ι 0) (c : r.X 0 ⟶ r'.X (Int.negSucc 0))
    (hc : f = r.ι 0 ≫ c ≫ r'.π (Int.negSucc 0)) : Homotopy φ 0 :=
  Homotopy.mkCochainComplexInt φ (homotopyHom φ hφ c hc) fun n => by
    rw [complex_d, complex_d]
    exact homotopyHom_comm φ hφ c hc n

variable {φ : r.complex ⟶ r'.complex} {f : r.Z 0 ⟶ r'.Z 0}

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
projective-injective object, that is, `f` vanishes in the stable category. -/
theorem nonempty_homotopy_zero_iff (hφ : r.ι 0 ≫ φ.f 0 = f ≫ r'.ι 0) :
    Nonempty (Homotopy φ 0) ↔ E.projectiveInjective.FactorsThrough f :=
  ⟨fun ⟨h⟩ => factorsThrough_of_homotopy hφ h, fun hf => ⟨liftHomotopyZero φ hφ hf⟩⟩

/-- Two lifts of the same morphism are homotopic. -/
noncomputable def liftHomotopy {r r' : E.CompleteResolution} (f : r.Z 0 ⟶ r'.Z 0)
    (φ ψ : r.complex ⟶ r'.complex) (hφ : r.ι 0 ≫ φ.f 0 = f ≫ r'.ι 0)
    (hψ : r.ι 0 ≫ ψ.f 0 = f ≫ r'.ι 0) : Homotopy φ ψ :=
  Homotopy.equivSubZero.symm (liftHomotopyZero (f := 0) (φ - ψ)
    (by simp [Preadditive.comp_sub, hφ, hψ]) (ObjectProperty.FactorsThrough.zero _ _ _))

/-- The lift of the identity is homotopic to the identity. -/
noncomputable def liftIdHomotopy (r : E.CompleteResolution) :
    Homotopy (lift r r (𝟙 (r.Z 0))) (𝟙 r.complex) :=
  liftHomotopy (𝟙 _) _ _ (by simp) (by simp)

/-- The lift of a composite is homotopic to the composite of the lifts. -/
noncomputable def liftCompHomotopy (r r' r'' : E.CompleteResolution) (f : r.Z 0 ⟶ r'.Z 0)
    (g : r'.Z 0 ⟶ r''.Z 0) : Homotopy (lift r r'' (f ≫ g)) (lift r r' f ≫ lift r' r'' g) :=
  liftHomotopy (f ≫ g) _ _ (by simp) (by simp)

/-- **Uniqueness of complete resolutions up to homotopy.** Complete resolutions whose objects of
cycles in degree zero are isomorphic have homotopy equivalent complexes. -/
noncomputable def homotopyEquiv (r r' : E.CompleteResolution) (e : r.Z 0 ≅ r'.Z 0) :
    HomotopyEquiv r.complex r'.complex where
  hom := lift r r' e.hom
  inv := lift r' r e.inv
  homotopyHomInvId := (liftCompHomotopy r r' r e.hom e.inv).symm.trans
    (by simpa using liftIdHomotopy r)
  homotopyInvHomId := (liftCompHomotopy r' r r' e.inv e.hom).symm.trans
    (by simpa using liftIdHomotopy r')

end Homotopy

end CompleteResolution

end ExactStructure

end TauCeti
