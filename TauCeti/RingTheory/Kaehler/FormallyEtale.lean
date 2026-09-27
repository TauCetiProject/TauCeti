/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import Mathlib.LinearAlgebra.TensorProduct.Basis
public import Mathlib.RingTheory.Etale.Kaehler
public import Mathlib.RingTheory.Kaehler.JacobiZariski

/-!
# Kähler differentials along a formally étale extension

For a tower `R → S → T` with `T` formally étale over `S`, Mathlib's
`KaehlerDifferential.tensorKaehlerEquivOfFormallyEtale` identifies `T ⊗[S] Ω[S⁄R]` with
`Ω[T⁄R]`. This file records what that says about bases, and proves a converse.

An `S`-basis of `Ω[S⁄R]` becomes a `T`-basis of `Ω[T⁄R]` on the same index type, each basis
vector going to its image under `KaehlerDifferential.map`. The motivating application is a tower of
fields `k → K → F` with `F/K` separable algebraic, so that `Algebra.FormallyEtale.of_isSeparable`
supplies the hypothesis: the differentials of `F` over `k` are then computed by those of `K`
over `k`.

Conversely, if `T` is formally smooth over `R` and `T ⊗[S] Ω[S⁄R] → Ω[T⁄R]` is bijective, then `T`
is formally étale over `S`. By the Jacobi–Zariski sequence

`H¹(L_{T/R}) → H¹(L_{T/S}) → T ⊗[S] Ω[S⁄R] → Ω[T⁄R] → Ω[T⁄S] → 0`,

`Ω[T⁄S]` vanishes when the middle map is surjective, and `H¹(L_{T/S})` vanishes when it is
injective, since `H¹(L_{T/R}) = 0` by formal smoothness. The typical use is with `S` a polynomial
ring over `R`: if the differentials `d aᵢ` of elements `aᵢ` of a formally smooth `R`-algebra `T`
form a basis of `Ω[T⁄R]`, then `T` is formally étale over `R[Xᵢ]` via `Xᵢ ↦ aᵢ`.

## Main declarations

* `TauCeti.kaehlerBasisOfFormallyEtale`: the induced basis of `Ω[T⁄R]`;
* `TauCeti.formallyEtale_of_bijective_mapBaseChange` and
  `TauCeti.formallyEtale_iff_bijective_mapBaseChange`: formal étaleness of `T` over `S` when `T`
  is formally smooth over `R`;
* `TauCeti.bijective_mapBaseChange_of_basis`: `T ⊗[S] Ω[S⁄R] → Ω[T⁄R]` is bijective when it
  carries a basis to a basis.

## References

* The Stacks Project, Tag 00S2, for the Jacobi–Zariski sequence.
-/

public section

noncomputable section

namespace TauCeti

open Module TensorProduct KaehlerDifferential

variable (R S T : Type*) [CommRing R] [CommRing S] [CommRing T] [Algebra R S] [Algebra R T]
  [Algebra S T] [IsScalarTower R S T]

section Basis

variable [Algebra.FormallyEtale S T]

/-- The `T`-basis of `Ω[T⁄R]` induced by an `S`-basis of `Ω[S⁄R]`, when `T` is formally étale
over `S`. Its vectors are the images of the given ones under `KaehlerDifferential.map`, as
recorded in `TauCeti.kaehlerBasisOfFormallyEtale_apply`. -/
def kaehlerBasisOfFormallyEtale {ι : Type*} (b : Basis ι S Ω[S⁄R]) : Basis ι T Ω[T⁄R] :=
  (b.baseChange T).map (KaehlerDifferential.tensorKaehlerEquivOfFormallyEtale R S T)

@[simp]
theorem kaehlerBasisOfFormallyEtale_apply {ι : Type*} (b : Basis ι S Ω[S⁄R]) (i : ι) :
    kaehlerBasisOfFormallyEtale R S T b i = KaehlerDifferential.map R R S T (b i) := by
  simp [kaehlerBasisOfFormallyEtale, KaehlerDifferential.mapBaseChange_tmul]

end Basis

variable {R S T}

/-- If `T` is formally smooth over `R` and `T ⊗[S] Ω[S⁄R] → Ω[T⁄R]` is bijective, then `T` is
formally étale over `S`. -/
theorem formallyEtale_of_bijective_mapBaseChange [Algebra.FormallySmooth R T]
    (h : Function.Bijective (mapBaseChange R S T)) : Algebra.FormallyEtale S T := by
  refine ⟨subsingleton_of_forall_eq 0 fun x ↦ ?_, subsingleton_of_forall_eq 0 fun x ↦ ?_⟩
  · -- `Ω[T⁄R] → Ω[T⁄S]` is onto, and its kernel is the image of `T ⊗[S] Ω[S⁄R]`, which is all.
    obtain ⟨y, rfl⟩ := map_surjective R S T x
    have hker := LinearMap.exact_iff.mp (exact_mapBaseChange_map R S T)
    rw [LinearMap.range_eq_top.mpr h.2] at hker
    exact LinearMap.mem_ker.mp (hker ▸ Submodule.mem_top)
  · -- `δ` vanishes since `mapBaseChange` is injective, so `x` comes from `H¹(L_{T/R}) = 0`.
    have hδ : Algebra.H1Cotangent.δ R S T x = 0 := by
      have hx : Algebra.H1Cotangent.δ R S T x ∈ LinearMap.ker (mapBaseChange R S T) := by
        rw [LinearMap.exact_iff.mp (Algebra.H1Cotangent.exact_δ_mapBaseChange R S T)]
        exact LinearMap.mem_range_self _ x
      exact h.1 (by rw [LinearMap.mem_ker.mp hx, map_zero])
    obtain ⟨y, rfl⟩ := (Algebra.H1Cotangent.exact_map_δ R S T x).mp hδ
    rw [Subsingleton.elim y 0, map_zero]

/-- For `T` formally smooth over `R`, `T` is formally étale over `S` exactly when
`T ⊗[S] Ω[S⁄R] → Ω[T⁄R]` is bijective. -/
theorem formallyEtale_iff_bijective_mapBaseChange [Algebra.FormallySmooth R T] :
    Algebra.FormallyEtale S T ↔ Function.Bijective (mapBaseChange R S T) :=
  ⟨fun _ ↦ (tensorKaehlerEquivOfFormallyEtale R S T).bijective,
    formallyEtale_of_bijective_mapBaseChange⟩

/-- The map `T ⊗[S] Ω[S⁄R] → Ω[T⁄R]` is bijective when it carries the base change of a basis of
`Ω[S⁄R]` to a basis of `Ω[T⁄R]`. -/
theorem bijective_mapBaseChange_of_basis {ι : Type*} (bS : Basis ι S Ω[S⁄R])
    (bT : Basis ι T Ω[T⁄R]) (h : ∀ i, map R R S T (bS i) = bT i) :
    Function.Bijective (mapBaseChange R S T) := by
  have : mapBaseChange R S T = ((bS.baseChange T).equiv bT (Equiv.refl ι)).toLinearMap :=
    (bS.baseChange T).ext fun i ↦ by
      simp only [LinearEquiv.coe_coe, Basis.equiv_apply, Equiv.refl_apply]
      simpa using h i
  rw [this]
  exact LinearEquiv.bijective _

end TauCeti
