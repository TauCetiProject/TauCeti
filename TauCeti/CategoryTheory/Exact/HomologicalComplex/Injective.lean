/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.Algebra.Homology.Homotopy
public import TauCeti.CategoryTheory.Exact.Acyclic
public import TauCeti.CategoryTheory.Exact.Injective
public import Mathlib.Algebra.Homology.Embedding.CochainComplex
public import Mathlib.Algebra.Homology.HomotopyCategory.Shift

/-!
# Maps from acyclic complexes to complexes of injectives

Let `E` be an exact structure. A map `φ : A ⟶ I` from an `E`-acyclic complex to a bounded below
complex of `E`-injective objects is null-homotopic. This is the dual of Bühler's Corollary 12.5 (no
maps from right bounded complexes of projectives to acyclic complexes), and the basic input for
computing morphisms into complexes of injectives in the derived category of `E`.

The null-homotopy `hⁿ : Aⁿ⁺¹ ⟶ Iⁿ` is built upwards from the lower bound of `I`. Write the
differentials of `A` as `Aⁿ ↠ Zⁿ⁺¹ ↣ Aⁿ⁺¹`. If `φⁿ⁺¹ - hⁿ ≫ d` vanishes on `Zⁿ⁺¹`, it descends to
`Zⁿ⁺² ⟶ Iⁿ⁺¹`, whose extension across `Zⁿ⁺² ↣ Aⁿ⁺²` into the injective `Iⁿ⁺¹` is `hⁿ⁺¹`; the next
difference `φⁿ⁺² - hⁿ⁺¹ ≫ d` again vanishes on `Zⁿ⁺²`, since `Aⁿ⁺¹ ↠ Zⁿ⁺²` is an epimorphism.

## Main definitions

* `TauCeti.ExactStructure.AcyclicData.homotopyZero`: the null-homotopy, for `I` strictly bounded
  below at `0`.

## Main results

* `TauCeti.ExactStructure.AcyclicData.quotient_map_eq_zero`: a map from an acyclic complex to a
  bounded below complex of injectives vanishes in the homotopy category.

## References

* Theo Bühler, *Exact categories*, Expositiones Mathematicae **28** (2010), 1--69,
  <https://arxiv.org/abs/0811.1480>, Corollary 12.5, of which this is the dual.
-/

public section

namespace TauCeti.ExactStructure

open CategoryTheory CategoryTheory.Limits

universe v u

variable {C : Type u} [Category.{v} C] [Preadditive C] [HasZeroObject C] [HasBinaryBiproducts C]
  {E : ExactStructure C}

namespace AcyclicData

variable {A I : CochainComplex C ℤ} (hA : E.AcyclicData A)

/-- The morphism out of the cycles `Zⁿ⁺¹` induced by a morphism out of `Aⁿ` killing `Zⁿ ↣ Aⁿ`. -/
noncomputable def descZ {T : C} (n : ℤ) (k : A.X n ⟶ T) (hk : hA.i n ≫ k = 0) : hA.Z (n + 1) ⟶ T :=
  (E.isKernelCokernelPair _ (hA.conflation n)).desc k hk

@[reassoc (attr := simp)]
theorem p_descZ {T : C} (n : ℤ) (k : A.X n ⟶ T) (hk : hA.i n ≫ k = 0) :
    hA.p n ≫ hA.descZ n k hk = k :=
  (E.isKernelCokernelPair _ (hA.conflation n)).g_desc k hk

instance (n : ℤ) : Epi (hA.p n) := (E.isDeflation_g (hA.conflation n)).epi

variable (hI : ∀ n, E.isInjective (I.X n)) (φ : A ⟶ I)

/-- The cancellation behind each step: if `d ≫ h' ≫ d = φ ≫ d` in degree `m`, then
`φᵐ⁺¹ - h' ≫ d` vanishes on `Zᵐ⁺¹`, since `Aᵐ ↠ Zᵐ⁺¹` is an epimorphism. -/
private theorem i_comp_sub_eq_zero_of (m : ℤ) (h' : A.X (m + 1) ⟶ I.X m)
    (H : A.d m (m + 1) ≫ h' ≫ I.d m (m + 1) = φ.f m ≫ I.d m (m + 1)) :
    hA.i (m + 1) ≫ (φ.f (m + 1) - h' ≫ I.d m (m + 1)) = 0 := by
  rw [← cancel_epi (hA.p m), comp_zero, ← Category.assoc, hA.fac, Preadditive.comp_sub,
    ← φ.comm, H, sub_self]

include hI in
/-- One step of the null-homotopy: a correction `χ : Aⁿ⁺¹ ⟶ Iⁿ⁺¹` vanishing on `Zⁿ⁺¹` and agreeing
with `φⁿ⁺¹` after the differential gives `h' : Aⁿ⁺² ⟶ Iⁿ⁺¹` with `d ≫ h' = χ`, and the next
correction `φⁿ⁺² - h' ≫ d` vanishes on `Zⁿ⁺²`. -/
private noncomputable def homUp (n : ℤ) (χ : A.X (n + 1) ⟶ I.X (n + 1))
    (hχ : hA.i (n + 1) ≫ χ = 0)
    (hχd : χ ≫ I.d (n + 1) (n + 1 + 1) = φ.f (n + 1) ≫ I.d (n + 1) (n + 1 + 1)) :
    { h' : A.X (n + 1 + 1) ⟶ I.X (n + 1) //
      A.d (n + 1) (n + 1 + 1) ≫ h' = χ ∧
        hA.i (n + 1 + 1) ≫ (φ.f (n + 1 + 1) - h' ≫ I.d (n + 1) (n + 1 + 1)) = 0 } :=
  let h' := (hI (n + 1)).factorThru (E.isInflation_f (hA.conflation (n + 1 + 1)))
    (hA.descZ (n + 1) χ hχ)
  have hd : A.d (n + 1) (n + 1 + 1) ≫ h' = χ := by
    rw [← hA.fac, Category.assoc]
    simp [h']
  ⟨h', hd, i_comp_sub_eq_zero_of hA φ (n + 1) h' (by rw [reassoc_of% hd, hχd])⟩

omit [HasZeroObject C] [HasBinaryBiproducts C] in
/-- The correction following a step agrees with `φ` after the differential. -/
private theorem sub_comp_d_eq (n : ℤ) (h' : A.X (n + 1) ⟶ I.X n) :
    (φ.f (n + 1) - h' ≫ I.d n (n + 1)) ≫ I.d (n + 1) (n + 1 + 1) =
      φ.f (n + 1) ≫ I.d (n + 1) (n + 1 + 1) := by
  rw [Preadditive.sub_comp, Category.assoc, HomologicalComplex.d_comp_d, comp_zero, sub_zero]

variable [I.IsStrictlyGE 0]

/-- The start of the recursion: the correction `φ⁰ - 0 ≫ d` vanishes on `Z⁰`, since `I⁻¹ = 0`. -/
private theorem i_comp_sub_eq_zero_zero :
    hA.i (Int.negSucc 0 + 1) ≫ (φ.f (Int.negSucc 0 + 1) - 0 ≫ I.d (Int.negSucc 0) 0) = 0 :=
  i_comp_sub_eq_zero_of hA φ (Int.negSucc 0) 0 (by
    rw [(I.isZero_of_isStrictlyGE 0 (Int.negSucc 0) (by decide)).eq_of_tgt (φ.f _) 0]
    simp)

include hI in
/-- The components `Aᵏ⁺¹ ⟶ Iᵏ` of the null-homotopy in nonnegative degrees. -/
private noncomputable def homPos : ∀ k : ℕ,
    { h : A.X ((k : ℤ) + 1) ⟶ I.X k //
      hA.i ((k : ℤ) + 1) ≫ (φ.f ((k : ℤ) + 1) - h ≫ I.d k (k + 1)) = 0 }
  | 0 =>
      let H := homUp hA hI φ (Int.negSucc 0) _ (i_comp_sub_eq_zero_zero hA φ)
        (sub_comp_d_eq φ (Int.negSucc 0) 0)
      ⟨H.1, H.2.2⟩
  | k + 1 =>
      let H := homUp hA hI φ k _ (homPos k).2 (sub_comp_d_eq φ k (homPos k).1)
      ⟨H.1, H.2.2⟩

/-- The components `Aⁿ⁺¹ ⟶ Iⁿ` of the null-homotopy: zero in negative degrees, where `I` is zero. -/
private noncomputable def homotopyHom : ∀ n : ℤ, A.X (n + 1) ⟶ I.X n
  | Int.ofNat k => (homPos hA hI φ k).1
  | Int.negSucc _ => 0

private theorem comm_ofNat (k : ℕ) :
    φ.f (Int.ofNat k + 1) = A.d (Int.ofNat k + 1) (Int.ofNat k + 1 + 1) ≫
      homotopyHom hA hI φ (Int.ofNat k + 1) +
        homotopyHom hA hI φ (Int.ofNat k) ≫ I.d (Int.ofNat k) (Int.ofNat k + 1) := by
  rw [← sub_eq_iff_eq_add]
  exact (homUp hA hI φ k _ (homPos hA hI φ k).2 (sub_comp_d_eq φ k (homPos hA hI φ k).1)).2.1.symm

private theorem comm_negSucc_zero :
    φ.f (Int.negSucc 0 + 1) = A.d (Int.negSucc 0 + 1) (Int.negSucc 0 + 1 + 1) ≫
      homotopyHom hA hI φ (Int.negSucc 0 + 1) +
        homotopyHom hA hI φ (Int.negSucc 0) ≫ I.d (Int.negSucc 0) (Int.negSucc 0 + 1) := by
  rw [← sub_eq_iff_eq_add]
  exact (homUp hA hI φ (Int.negSucc 0) _ (i_comp_sub_eq_zero_zero hA φ)
    (sub_comp_d_eq φ (Int.negSucc 0) 0)).2.1.symm

private theorem comm_negSucc_succ (k : ℕ) :
    φ.f (Int.negSucc (k + 1) + 1) =
      A.d (Int.negSucc (k + 1) + 1) (Int.negSucc (k + 1) + 1 + 1) ≫
        homotopyHom hA hI φ (Int.negSucc (k + 1) + 1) +
          homotopyHom hA hI φ (Int.negSucc (k + 1)) ≫
            I.d (Int.negSucc (k + 1)) (Int.negSucc (k + 1) + 1) :=
  (I.isZero_of_isStrictlyGE 0 _ (by omega)).eq_of_tgt _ _

/-- **Maps from acyclic complexes to complexes of injectives are null-homotopic**: a map from an
`E`-acyclic complex to a complex of `E`-injective objects that vanishes in negative degrees. -/
noncomputable def homotopyZero : Homotopy φ 0 :=
  Homotopy.mkCochainComplexInt φ (homotopyHom hA hI φ) fun n => by
    match n with
    | Int.ofNat k => exact comm_ofNat hA hI φ k
    | Int.negSucc 0 => exact comm_negSucc_zero hA hI φ
    | Int.negSucc (k + 1) => exact comm_negSucc_succ hA hI φ k

omit [I.IsStrictlyGE 0]

include hA hI in
/-- **Maps from acyclic complexes to bounded below complexes of injectives vanish in the homotopy
category**: the dual of Bühler's Corollary 12.5. The bound is moved to `0` by shifting. -/
theorem quotient_map_eq_zero (n : ℤ) [I.IsStrictlyGE n] :
    (HomotopyCategory.quotient C (.up ℤ)).map φ = 0 := by
  have : (I⟦n⟧).IsStrictlyGE 0 := I.isStrictlyGE_shift n n 0 (by simp)
  have h := HomotopyCategory.eq_of_homotopy _ _
    ((hA.shift n).homotopyZero (fun k ↦ hI (k + n)) (φ⟦n⟧'))
  rw [Functor.map_zero] at h
  apply (shiftFunctor (HomotopyCategory C (.up ℤ)) n).map_injective
  rw [Functor.map_zero, ← cancel_epi (((HomotopyCategory.quotient C (.up ℤ)).commShiftIso n).hom.app
    A), ← Functor.commShiftIso_hom_naturality, h, zero_comp, comp_zero]

end AcyclicData

end TauCeti.ExactStructure
