/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.Algebra.Coalgebra.Comodule.Induced
public import TauCeti.Algebra.Coalgebra.Comodule.LinearlyReductive
import TauCeti.Algebra.Coalgebra.Comodule.LinearlyReductive.Fixed
import TauCeti.LinearAlgebra.TensorProduct.Basic

/-!
# Invariant surjectivity along colinear sections

Let `q : C →ₗc[R] D` be a morphism of coalgebras with `C` flat over `R`. Any `R`-linear map
`σ : D →ₗ[R] C` intertwining `(q ⊗ id) ∘ Δ_C ∘ σ = (id ⊗ σ) ∘ Δ_D` sends the coaction of a
right `D`-comodule `M` into the induced `C`-comodule `Ind_q M`.

Over a field `k`, when `q : C →ₐc[k] D` is a morphism of bialgebras, `C` is linearly reductive,
and `σ 1 = 1`, this embedding into induced comodules transfers surjectivity on invariants from `C`
to `D` for arbitrary right `D`-comodules `M` and `N`. For affine group schemes `H ≤ G`, such a
unital left `O(H)`-colinear section `O(H) →ₗ[k] O(G)` arises whenever the coset quotient `G / H`
admits a global section, for instance when `H = G°` over an algebraically closed field.

## Main declarations

* `TauCeti.Comodule.lTensor_coact_mem_induced`: pushing a `D`-coaction along a left-colinear linear
  map `D →ₗ[R] C` lands in `TauCeti.Comodule.induced`.
* `TauCeti.Comodule.Hom.fixedMap_surjective_of_colinear_section`: surjectivity on invariants
  descends from a linearly reductive bialgebra `C` to any bialgebra `D` along a bialgebra morphism
  admitting a unital left-colinear linear section.

## References

* J. C. Jantzen, *Representations of Algebraic Groups*, 2nd ed., I.3.3–I.3.4 and I.4.
* J. S. Milne, *Algebraic Groups* (2017), Section 12.g.
-/

public section

open scoped TensorProduct

namespace TauCeti.Comodule

universe u v w x y

attribute [local instance] cofree

/-- Pushing the coaction of a vector in a right `D`-comodule along an `R`-linear map
`σ : D →ₗ[R] C` satisfying `(f ⊗ id) ∘ Δ_C ∘ σ = (id ⊗ σ) ∘ Δ_D` produces an element of the
induced `C`-comodule `Ind_f M`. -/
theorem lTensor_coact_mem_induced {R : Type u} [CommRing R] {C : Type v} {D : Type w}
    [AddCommMonoid C] [Module R C] [Coalgebra R C] [Module.Flat R C]
    [AddCommMonoid D] [Module R D] [Coalgebra R D]
    {f : C →ₗc[R] D} {σ : D →ₗ[R] C}
    (hσ : ∀ x : D,
      ((f : C →ₗ[R] D).rTensor C) (Coalgebra.comul (R := R) (σ x)) =
        σ.lTensor D (Coalgebra.comul (R := R) x))
    {M : Type x} [AddCommMonoid M] [Module R M] [Comodule R D M] (m : M) :
    σ.lTensor M (coact (R := R) (C := D) m) ∈ induced f M := by
  rw [mem_induced_iff, ← LinearMap.lTensor_rTensor_comm]
  have hcoassoc :
      (coact (R := R) (C := D) (M := M)).rTensor D (coact (R := R) (C := D) m) =
        (TensorProduct.assoc R M D D).symm
          ((Coalgebra.comul (R := R) (A := D)).lTensor M (coact (R := R) (C := D) m)) :=
    (TensorProduct.assoc R M D D).eq_symm_apply.mpr
      (LinearMap.congr_fun (coact_coassoc (R := R) (C := D) (M := M)) m)
  rw [hcoassoc]
  have h2 (z : M ⊗[R] D) :
      σ.lTensor (M ⊗[R] D)
          ((TensorProduct.assoc R M D D).symm
            ((Coalgebra.comul (R := R) (A := D)).lTensor M z)) =
        (TensorProduct.assoc R M D C).symm
          (((f : C →ₗ[R] D).rTensor C ∘ₗ Coalgebra.comul).lTensor M (σ.lTensor M z)) := by
    induction z using TensorProduct.inductionOn with
    | tmul v x =>
      simp only [LinearMap.lTensor_tmul, LinearMap.comp_apply]
      rw [hσ x]
      induction Coalgebra.comul (R := R) x using TensorProduct.inductionOn with
      | tmul x₁ x₂ => simp
      | add y w hy hw => simp [TensorProduct.tmul_add, hy, hw]
    | add y w hy hw => simp [hy, hw]
  exact h2 (coact (R := R) (C := D) m)

/-- Applying `inducedMap q φ` to `(id ⊗ σ)(ρ m₀)` for a preimage `m₀` of a `D`-fixed vector `n`
produces a `C`-fixed element of `Ind_q N` with underlying tensor `n ⊗ 1`. -/
private theorem inducedMap_lTensor_coact_fixed {R : Type u} [CommRing R]
    {C : Type v} {D : Type w} [Semiring C] [Bialgebra R C] [Module.Flat R C]
    [Semiring D] [Bialgebra R D]
    {q : C →ₗc[R] D} {σ : D →ₗ[R] C} (hσ1 : σ 1 = 1)
    (hσ : ∀ x : D,
      ((q : C →ₗ[R] D).rTensor C) (Coalgebra.comul (R := R) (σ x)) =
        σ.lTensor D (Coalgebra.comul (R := R) x))
    {M : Type x} {N : Type y} [AddCommMonoid M] [Module R M] [Comodule R D M]
    [AddCommMonoid N] [Module R N] [Comodule R D N]
    (φ : Hom R D M N) {m₀ : M} {n : N} (hm₀ : φ m₀ = n)
    (hn : n ∈ fixedSubcomodule R D N) :
    let t : induced q M :=
      ⟨σ.lTensor M (coact (R := R) (C := D) m₀), lTensor_coact_mem_induced hσ m₀⟩
    (inducedMap q φ t : N ⊗[R] C) = n ⊗ₜ[R] (1 : C) ∧
      inducedMap q φ t ∈ fixedSubcomodule R C (induced q N) := by
  intro t
  have hy_coe : (inducedMap q φ t : N ⊗[R] C) = n ⊗ₜ[R] (1 : C) := by
    rw [coe_inducedMap_apply]
    simp only [t]
    rw [← LinearMap.lTensor_rTensor_comm, LinearMap.rTensor_def,
      φ.map_coact_apply m₀, hm₀, mem_fixedSubcomodule.mp hn, LinearMap.lTensor_tmul, hσ1]
  refine ⟨hy_coe, ?_⟩
  rw [mem_fixedSubcomodule]
  apply Module.Flat.rTensor_preserves_injective_linearMap
    (SMulMemClass.subtype (induced q N)) Subtype.val_injective
  rw [Subcomodule.subtype_rTensor_coact, LinearMap.rTensor_tmul, SMulMemClass.subtype_apply,
    hy_coe, cofree_coact]
  simp [Bialgebra.comul_one, Algebra.TensorProduct.one_def]

/-- Over a field `k`, if a linearly reductive bialgebra `C` maps to a bialgebra `D` via
`q : C →ₐc[k] D` admitting a unital `k`-linear map `σ : D →ₗ[k] C` that intertwines
`(q ⊗ id) ∘ Δ_C ∘ σ = (id ⊗ σ) ∘ Δ_D`, then every surjective morphism of right `D`-comodules
remains surjective on `D`-fixed vectors. -/
theorem Hom.fixedMap_surjective_of_colinear_section {k : Type u} [Field k]
    {C : Type v} {D : Type w} [Semiring C] [Bialgebra k C] [Semiring D] [Bialgebra k D]
    (q : C →ₐc[k] D) (σ : D →ₗ[k] C) (hσ1 : σ 1 = 1)
    (hσ : ∀ x : D,
      ((q.toCoalgHom : C →ₗ[k] D).rTensor C) (Coalgebra.comul (R := k) (σ x)) =
        σ.lTensor D (Coalgebra.comul (R := k) x))
    (hC : Coalgebra.IsLinearlyReductive.{u, v, u} k C)
    {M : Type x} {N : Type y} [AddCommMonoid M] [Module k M] [Comodule k D M]
    [AddCommMonoid N] [Module k N] [Comodule k D N]
    (φ : Hom k D M N) (hφ : Function.Surjective φ) :
    Function.Surjective φ.fixedMap := by
  let _ : AddCommGroup C := Module.addCommMonoidToAddCommGroup k
  let _ : Module.Free k C := Module.Free.of_divisionRing k C
  let _ : AddCommGroup M := Module.addCommMonoidToAddCommGroup k
  let _ : AddCommGroup N := Module.addCommMonoidToAddCommGroup k
  intro n
  obtain ⟨m₀, hm₀⟩ := hφ n.1
  let t : induced q.toCoalgHom M :=
    ⟨σ.lTensor M (coact (R := k) (C := D) m₀), lTensor_coact_mem_induced hσ m₀⟩
  obtain ⟨hy_coe, hy_fixed⟩ := inducedMap_lTensor_coact_fixed hσ1 hσ φ hm₀ n.2
  obtain ⟨x, hx_fixed, hxy⟩ :=
    (inducedMap q.toCoalgHom φ).exists_fixed_preimage_of_isLinearlyReductive hC hy_fixed ⟨t, rfl⟩
  let m : M := TensorProduct.rid k M ((Coalgebra.counit (R := k) (A := C)).lTensor M x)
  have hm_fixed : m ∈ fixedSubcomodule k D M := by
    let _ : Comodule k D (induced q.toCoalgHom M) := Corestrict q.toCoalgHom
    have hq1 : q.toCoalgHom 1 = 1 := map_one q
    have hx_corestrict : x ∈ fixedSubcomodule k D (induced q.toCoalgHom M) := by
      rw [Comodule.mem_fixedSubcomodule, corestrict_coact_apply,
        Comodule.mem_fixedSubcomodule.mp hx_fixed]
      simp [hq1]
    simpa only [inducedEval_apply] using
      (inducedEval q.toCoalgHom).mem_fixedSubcomodule hx_corestrict
  have hφm : φ m = n.1 := by
    have hnat := LinearMap.congr_fun
      (rid_comp_lTensor_counit_comp_rTensor (C := C) φ.toLinearMap) (x : M ⊗[k] C)
    simp only [LinearMap.comp_apply] at hnat
    calc
      φ m = TensorProduct.rid k N
          ((Coalgebra.counit (R := k) (A := C)).lTensor N (φ.toLinearMap.rTensor C x)) :=
        hnat.symm
      _ = TensorProduct.rid k N
          ((Coalgebra.counit (R := k) (A := C)).lTensor N (n.1 ⊗ₜ[k] (1 : C))) := by
        rw [← coe_inducedMap_apply q.toCoalgHom φ x, hxy, hy_coe]
      _ = n.1 := by simp
  exact ⟨⟨m, hm_fixed⟩, Subtype.ext ((φ.fixedMap_apply ⟨m, hm_fixed⟩).trans hφm)⟩

end TauCeti.Comodule
