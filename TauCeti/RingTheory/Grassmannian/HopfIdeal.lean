/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import Mathlib.RingTheory.HopfAlgebra.Quotient
public import TauCeti.Algebra.Coalgebra.BaseChange
public import TauCeti.Algebra.HopfAlgebra.BaseChange
public import TauCeti.RingTheory.Grassmannian.ClosedCondition

/-!
# The closed locus of Hopf ideals in the Grassmannian

Let `H` be a Hopf algebra over a commutative ring `R`. A point of the Grassmannian functor
`A ↦ G(k, A ⊗[R] H; A)` is an `A`-submodule `N` of `A ⊗[R] H` whose quotient is finite projective
of constant rank `k`. When `N` is a two-sided Hopf ideal, the quotient is a Hopf algebra over `A`,
so for commutative `H` the closed subscheme `Spec ((A ⊗[R] H) ⧸ N)` is a subgroup scheme of the
base change of `Spec H` to `A`, finite locally free of rank `k` over `A`. This file shows that being
a two-sided Hopf ideal is a closed condition on the Grassmannian: there is an ideal
`N.hopfIdealLocus` of `A` such that, for every `R`-algebra map `f : A → B`, the base change of `N`
to `B` is a two-sided Hopf ideal of `B ⊗[R] H` exactly when `f` kills `N.hopfIdealLocus`
(`Module.Grassmannian.hopfIdealLocus_le_ker_iff`). The formation of the ideal commutes with base
change (`Module.Grassmannian.hopfIdealLocus_map`). This is the input for cutting out, inside the
Grassmannian scheme, the closed subscheme which parametrises the subgroup schemes of rank `k`.

The ideal is the sum of five contents, one for each condition. Write `π : A ⊗[R] H → Q` for the
quotient by `N`. The image of `N` under the counit, under `π ∘ S` for the antipode `S`, under
`(π ⊗ π) ∘ Δ` for the comultiplication `Δ`, under `π ∘ (1 ⊗ₜ h) * -` and under `π ∘ - * (1 ⊗ₜ h)`
for each `h : H` is a submodule of a finite projective `A`-module (`A`, `Q`, `Q ⊗[A] Q`, `Q` and
`Q`), and its content (`Submodule.minorsIdeal 1`) is the ideal along which it vanishes after base
change (`Module.Grassmannian.ker_baseChangeMkQ_le_ker_iff_minorsIdeal_le`). The counit and the
antipode commute with base change (`LinearMap.counit_rTensor` and
`TensorProduct.antipode_rTensor`). For commutative `H` the last two summands coincide.

## Main definitions

* `Module.Grassmannian.hopfIdealLocus N`: the ideal of `A` cutting out the locus where `N` is a
  two-sided Hopf ideal.

## Main results

* `Module.Grassmannian.hopfIdealLocus_le_ker_iff`: the base change of `N` along `f` is a two-sided
  Hopf ideal exactly when `f` kills `N.hopfIdealLocus`.
* `Module.Grassmannian.hopfIdealLocus_eq_bot_iff`: `N` itself is a two-sided Hopf ideal exactly
  when `N.hopfIdealLocus = ⊥`.
* `Module.Grassmannian.hopfIdealLocus_map`: the formation of `hopfIdealLocus` commutes with base
  change.

## References

* [The Stacks Project, Tag 089R](https://stacks.math.columbia.edu/tag/089R), for the Grassmannian
  functor.
-/

public section

universe u v w

open TensorProduct

namespace Module.Grassmannian

variable {R : Type u} [CommRing R] {k : ℕ} {A B : Type w} [CommRing A] [Algebra R A]
  [CommRing B] [Algebra R B]

variable {H : Type v} [Ring H] [HopfAlgebra R H]

/-- The **locus of Hopf ideals**: for a point `N` of the Grassmannian of rank-`k` quotients of
`A ⊗[R] H`, the ideal of `A` killed by an `R`-algebra map `f : A → B` exactly when the base change
of `N` to `B` is a two-sided Hopf ideal of `B ⊗[R] H`
(`Module.Grassmannian.hopfIdealLocus_le_ker_iff`).

With `π : A ⊗[R] H → Q` the quotient by `N`, it is the sum of the contents of the images of `N`
under the counit, under `π ∘ S` for the antipode `S`, under `(π ⊗ π) ∘ Δ` for the
comultiplication `Δ`, and under `π ∘ (1 ⊗ₜ h) * -` and `π ∘ - * (1 ⊗ₜ h)` for all `h : H`. -/
noncomputable def hopfIdealLocus (N : G(k, A ⊗[R] H; A)) : Ideal A :=
  (N.toSubmodule.map (Coalgebra.counit (R := A) (A := A ⊗[R] H))).minorsIdeal 1 ⊔
    (N.toSubmodule.map (N.toSubmodule.mkQ ∘ₗ HopfAlgebra.antipode A)).minorsIdeal 1 ⊔
    (N.toSubmodule.map (TensorProduct.map N.toSubmodule.mkQ N.toSubmodule.mkQ ∘ₗ
      Coalgebra.comul (R := A))).minorsIdeal 1 ⊔
    (⨆ h : H, (N.toSubmodule.map
      (N.toSubmodule.mkQ ∘ₗ LinearMap.mulLeft A ((1 : A) ⊗ₜ[R] h))).minorsIdeal 1) ⊔
    ⨆ h : H, (N.toSubmodule.map
      (N.toSubmodule.mkQ ∘ₗ LinearMap.mulRight A ((1 : A) ⊗ₜ[R] h))).minorsIdeal 1

section BaseChange

variable [Algebra A B] [IsScalarTower R A B]

/-- The comultiplication of `B ⊗[R] H`, followed by the base change of `π ⊗ π`, is the base change
of `(π ⊗ π) ∘ Δ`. -/
private theorem map_baseChangeMkQ_comul_rTensor (N : Submodule A (A ⊗[R] H)) (x : A ⊗[R] H) :
    TensorProduct.map (baseChangeMkQ B N) (baseChangeMkQ B N)
        (Coalgebra.comul (R := B) ((IsScalarTower.toAlgHom R A B).toLinearMap.rTensor H x)) =
      AlgebraTensorModule.distribBaseChange A B _ _
        ((1 : B) ⊗ₜ TensorProduct.map N.mkQ N.mkQ (Coalgebra.comul (R := A) x)) := by
  induction x using TensorProduct.inductionOn with
  | tmul a h =>
    simp only [LinearMap.rTensor_tmul, AlgHom.toLinearMap_apply, IsScalarTower.coe_toAlgHom',
      TensorProduct.comul_tmul, CommSemiring.comul_apply]
    induction Coalgebra.comul (R := R) h using TensorProduct.inductionOn with
    | tmul h₁ h₂ =>
      simp only [map_tmul, baseChangeMkQ_tmul, AlgebraTensorModule.tensorTensorTensorComm_tmul,
        Submodule.mkQ_apply, AlgebraTensorModule.distribBaseChange_tmul]
      rw [tmul_eq_smul_one_tmul a h₂, Submodule.Quotient.mk_smul, tmul_smul, smul_tmul',
        Algebra.smul_def, mul_one]
    | add s t hs ht => simp only [tmul_add, map_add, hs, ht]
  | add x y hx hy => simp only [map_add, tmul_add, hx, hy]

/-- The five summands of `hopfIdealLocus` are killed by `A → B` exactly when the counit, the
antipode, the comultiplication and the left and right multiplications by the `1 ⊗ₜ h` are compatible
with the base change of `N` to `B`. -/
private theorem hopfIdealLocus_le_ker_algebraMap_iff_ker_le (N : G(k, A ⊗[R] H; A)) :
    N.hopfIdealLocus ≤ RingHom.ker (algebraMap A B) ↔
      (((LinearMap.ker (baseChangeMkQ B N.toSubmodule) ≤
          LinearMap.ker (Coalgebra.counit (R := B) (A := B ⊗[R] H)) ∧
        LinearMap.ker (baseChangeMkQ B N.toSubmodule) ≤
          LinearMap.ker (baseChangeMkQ B N.toSubmodule ∘ₗ HopfAlgebra.antipode B)) ∧
        LinearMap.ker (baseChangeMkQ B N.toSubmodule) ≤
          LinearMap.ker (TensorProduct.map (baseChangeMkQ B N.toSubmodule)
            (baseChangeMkQ B N.toSubmodule) ∘ₗ Coalgebra.comul (R := B))) ∧
        ∀ h : H, LinearMap.ker (baseChangeMkQ B N.toSubmodule) ≤
          LinearMap.ker
            (baseChangeMkQ B N.toSubmodule ∘ₗ LinearMap.mulLeft B ((1 : B) ⊗ₜ[R] h))) ∧
        ∀ h : H, LinearMap.ker (baseChangeMkQ B N.toSubmodule) ≤
          LinearMap.ker
            (baseChangeMkQ B N.toSubmodule ∘ₗ LinearMap.mulRight B ((1 : B) ⊗ₜ[R] h)) := by
  set Q := A ⊗[R] H ⧸ N.toSubmodule
  have hgQ := TensorProduct.isBaseChange A Q B
  have hcounit := ker_baseChangeMkQ_le_ker_iff_minorsIdeal_le N.toSubmodule
    (Coalgebra.counit (R := B) (A := B ⊗[R] H)) (Coalgebra.counit (R := A) (A := A ⊗[R] H))
    (IsBaseChange.linearMap A B) fun x ↦ LinearMap.counit_rTensor _ x
  have hantipode := ker_baseChangeMkQ_le_ker_iff_minorsIdeal_le N.toSubmodule
    (baseChangeMkQ B N.toSubmodule ∘ₗ HopfAlgebra.antipode B)
    (N.toSubmodule.mkQ ∘ₗ HopfAlgebra.antipode A) hgQ fun x ↦ by
      rw [LinearMap.comp_apply, antipode_rTensor, baseChangeMkQ_rTensor, LinearMap.comp_apply,
        TensorProduct.mk_apply]
  let g : Q ⊗[A] Q →ₗ[A] (B ⊗[A] Q) ⊗[B] (B ⊗[A] Q) :=
    (AlgebraTensorModule.distribBaseChange A B Q Q).toLinearMap.restrictScalars A ∘ₗ
      TensorProduct.mk A B (Q ⊗[A] Q) 1
  have hg : IsBaseChange B g :=
    IsBaseChange.of_equiv (AlgebraTensorModule.distribBaseChange A B Q Q) fun _ ↦ rfl
  -- the module types are given explicitly to keep elaboration from unfolding the tensor products
  have hcomul := ker_baseChangeMkQ_le_ker_iff_minorsIdeal_le (X := Q ⊗[A] Q)
    (Y := (B ⊗[A] Q) ⊗[B] (B ⊗[A] Q)) N.toSubmodule
    (TensorProduct.map (baseChangeMkQ B N.toSubmodule) (baseChangeMkQ B N.toSubmodule) ∘ₗ
      Coalgebra.comul (R := B))
    (TensorProduct.map N.toSubmodule.mkQ N.toSubmodule.mkQ ∘ₗ Coalgebra.comul (R := A)) hg
    fun x ↦ by
      rw [LinearMap.comp_apply, map_baseChangeMkQ_comul_rTensor]
      simp [g, Q]
  -- `f ⊗ id` is multiplicative, being the algebra map `Algebra.TensorProduct.map f (.id R H)`
  have hf : (Algebra.TensorProduct.map (IsScalarTower.toAlgHom R A B) (.id R H)).toLinearMap =
      (IsScalarTower.toAlgHom R A B).toLinearMap.rTensor H := by
    rw [Algebra.TensorProduct.toLinearMap_map, AlgebraTensorModule.map_eq, AlgHom.toLinearMap_id,
      LinearMap.rTensor]
  have hfmul (x y : A ⊗[R] H) : (IsScalarTower.toAlgHom R A B).toLinearMap.rTensor H (x * y) =
      (IsScalarTower.toAlgHom R A B).toLinearMap.rTensor H x *
        (IsScalarTower.toAlgHom R A B).toLinearMap.rTensor H y := by
    simp only [← hf, AlgHom.toLinearMap_apply, map_mul]
  have hf1 (h : H) :
      (IsScalarTower.toAlgHom R A B).toLinearMap.rTensor H ((1 : A) ⊗ₜ[R] h) = (1 : B) ⊗ₜ[R] h := by
    simp
  have hmul (h : H) := ker_baseChangeMkQ_le_ker_iff_minorsIdeal_le N.toSubmodule
    (baseChangeMkQ B N.toSubmodule ∘ₗ LinearMap.mulLeft B ((1 : B) ⊗ₜ[R] h))
    (N.toSubmodule.mkQ ∘ₗ LinearMap.mulLeft A ((1 : A) ⊗ₜ[R] h)) hgQ fun x ↦ by
      rw [LinearMap.comp_apply, LinearMap.mulLeft_apply, ← hf1, ← hfmul,
        baseChangeMkQ_rTensor, LinearMap.comp_apply, TensorProduct.mk_apply,
        LinearMap.mulLeft_apply]
  have hmulRight (h : H) := ker_baseChangeMkQ_le_ker_iff_minorsIdeal_le N.toSubmodule
    (baseChangeMkQ B N.toSubmodule ∘ₗ LinearMap.mulRight B ((1 : B) ⊗ₜ[R] h))
    (N.toSubmodule.mkQ ∘ₗ LinearMap.mulRight A ((1 : A) ⊗ₜ[R] h)) hgQ fun x ↦ by
      rw [LinearMap.comp_apply, LinearMap.mulRight_apply, ← hf1, ← hfmul,
        baseChangeMkQ_rTensor, LinearMap.comp_apply, TensorProduct.mk_apply,
        LinearMap.mulRight_apply]
  simp only [hopfIdealLocus, sup_le_iff, iSup_le_iff, ← hcounit, ← hantipode, ← hcomul, ← hmul,
    ← hmulRight]

/-- The universal property of `hopfIdealLocus`, for an algebra `B` over `A`. -/
private theorem hopfIdealLocus_le_ker_algebraMap_iff (N : G(k, A ⊗[R] H; A)) :
    N.hopfIdealLocus ≤ RingHom.ker (algebraMap A B) ↔
      ∃ I : Ideal (B ⊗[R] H), I.restrictScalars B = LinearMap.ker (baseChangeMkQ B N.toSubmodule) ∧
        I.IsTwoSided ∧ I.IsHopfIdeal B := by
  set π := baseChangeMkQ B N.toSubmodule
  set K := LinearMap.ker π
  -- `π` is the quotient map by `K` followed by an isomorphism, so `K` is a coideal exactly when
  -- `(π ⊗ π) ∘ Δ` vanishes on it
  let e := π.quotKerEquivOfSurjective (baseChangeMkQ_surjective N.toSubmodule)
  have he : (e : _ →ₗ[B] _) ∘ₗ K.mkQ = π :=
    LinearMap.ext fun x ↦
      LinearMap.quotKerEquivOfSurjective_apply_mk _ (baseChangeMkQ_surjective N.toSubmodule) x
  have hmap (t : (B ⊗[R] H) ⊗[B] (B ⊗[R] H)) :
      TensorProduct.map π π t = TensorProduct.congr e e (TensorProduct.map K.mkQ K.mkQ t) := by
    rw [← LinearEquiv.coe_toLinearMap, TensorProduct.congr, LinearEquiv.toLinearMap_ofLinearMap,
      ← LinearMap.comp_apply, ← TensorProduct.map_comp, he]
  have hcoideal : K.IsCoideal ↔ K ≤ LinearMap.ker (Coalgebra.counit (R := B)) ∧
      K ≤ LinearMap.ker (TensorProduct.map π π ∘ₗ Coalgebra.comul (R := B)) := by
    simp only [Submodule.isCoideal_iff, IsConcreteLE.le_iff, LinearMap.mem_ker,
      LinearMap.comp_apply, hmap, LinearEquiv.map_eq_zero_iff]
  rw [hopfIdealLocus_le_ker_algebraMap_iff_ker_le]
  constructor
  · rintro ⟨⟨⟨⟨hε, hS⟩, hΔ⟩, hμl⟩, hμr⟩
    -- `K` is a two-sided ideal, since `B ⊗[R] H` is spanned over `B` by the `1 ⊗ₜ h`
    have hmulK (c : B ⊗[R] H) {y : B ⊗[R] H} (hy : y ∈ K) : c * y ∈ K := by
      induction c using TensorProduct.inductionOn with
      | tmul b h =>
        rw [tmul_eq_smul_one_tmul b h, smul_mul_assoc]
        exact K.smul_mem b (hμl h hy)
      | add c d hc hd =>
        rw [add_mul]
        exact K.add_mem hc hd
    have hKmul (c : B ⊗[R] H) {y : B ⊗[R] H} (hy : y ∈ K) : y * c ∈ K := by
      induction c using TensorProduct.inductionOn with
      | tmul b h =>
        rw [tmul_eq_smul_one_tmul b h, mul_smul_comm]
        exact K.smul_mem b (hμr h hy)
      | add c d hc hd =>
        rw [mul_add]
        exact K.add_mem hc hd
    let I : Ideal (B ⊗[R] H) := { K.toAddSubmonoid with smul_mem' := fun c _ hy ↦ hmulK c hy }
    -- `I` is `K` with the larger scalar ring, so the two have the same underlying set
    have hI : I.restrictScalars B = K := rfl
    exact ⟨I, hI, ⟨fun c hy ↦ hKmul c hy⟩,
      { toIsCoideal := hI ▸ hcoideal.2 ⟨hε, hΔ⟩, antipode_mem := fun _ hy ↦ hS hy }⟩
  · rintro ⟨I, hI, hTwo, hHopf⟩
    have hmem (y : B ⊗[R] H) : y ∈ K ↔ y ∈ I := by rw [← hI, Submodule.restrictScalars_mem]
    obtain ⟨hε, hΔ⟩ := hcoideal.1 (hI ▸ hHopf.toIsCoideal)
    refine ⟨⟨⟨⟨hε, fun y hy ↦ ?_⟩, hΔ⟩, fun h y hy ↦ ?_⟩, fun h y hy ↦ ?_⟩
    · exact (hmem _).2 (hHopf.antipode_mem ((hmem y).1 hy))
    · exact (hmem _).2 (I.mul_mem_left _ ((hmem y).1 hy))
    · exact (hmem _).2 (hTwo.mul_mem_of_left _ ((hmem y).1 hy))

end BaseChange

/-- **Being a two-sided Hopf ideal is a closed condition on the Grassmannian.** For a point `N`
of `G(k, A ⊗[R] H; A)` and an `R`-algebra map `f : A → B`, the base change of `N` to `B` is a
two-sided Hopf ideal of `B ⊗[R] H` exactly when `f` kills `N.hopfIdealLocus`. -/
theorem hopfIdealLocus_le_ker_iff (f : A →ₐ[R] B) (N : G(k, A ⊗[R] H; A)) :
    N.hopfIdealLocus ≤ RingHom.ker f ↔
      ∃ I : Ideal (B ⊗[R] H), I.restrictScalars B = (map f N).toSubmodule ∧ I.IsTwoSided ∧
        I.IsHopfIdeal B := by
  algebraize [f.toRingHom]
  -- `algebraize` makes `f` the structure map of `B` as an `A`-algebra
  have hf : IsScalarTower.toAlgHom R A B = f := AlgHom.ext fun _ ↦ rfl
  rw [← hf, map_toAlgHom_toSubmodule]
  exact hopfIdealLocus_le_ker_algebraMap_iff N

/-- A point `N` of `G(k, A ⊗[R] H; A)` is a two-sided Hopf ideal of `A ⊗[R] H` exactly when
`N.hopfIdealLocus` vanishes. -/
theorem hopfIdealLocus_eq_bot_iff (N : G(k, A ⊗[R] H; A)) :
    N.hopfIdealLocus = ⊥ ↔
      ∃ I : Ideal (A ⊗[R] H), I.restrictScalars A = N.toSubmodule ∧ I.IsTwoSided ∧
        I.IsHopfIdeal A := by
  have hker : RingHom.ker (AlgHom.id R A) = ⊥ :=
    (RingHom.injective_iff_ker_eq_bot _).1 Function.injective_id
  rw [← le_bot_iff, ← hker, hopfIdealLocus_le_ker_iff, map_id k (.of R A) N]

/-- The formation of `hopfIdealLocus` commutes with base change. -/
@[simp]
theorem hopfIdealLocus_map (f : A →ₐ[R] B) (N : G(k, A ⊗[R] H; A)) :
    (map f N).hopfIdealLocus = Ideal.map f N.hopfIdealLocus := by
  -- both ideals are killed by the same `R`-algebra maps out of `B`; test on the quotients by each
  refine le_antisymm ?_ (Ideal.map_le_iff_le_comap.2 ?_)
  · let g := Ideal.Quotient.mkₐ R (Ideal.map f N.hopfIdealLocus)
    have h := (hopfIdealLocus_le_ker_iff (g.comp f) N).1 fun x hx ↦ by
      rw [RingHom.mem_ker, AlgHom.comp_apply, Ideal.Quotient.mkₐ_eq_mk,
        Ideal.Quotient.eq_zero_iff_mem]
      exact Ideal.mem_map_of_mem f hx
    rw [map_comp] at h
    exact ((hopfIdealLocus_le_ker_iff g (map f N)).2 h).trans (Ideal.Quotient.mkₐ_ker R _).le
  · let g := Ideal.Quotient.mkₐ R (map f N).hopfIdealLocus
    have h := (hopfIdealLocus_le_ker_iff g (map f N)).1 (Ideal.Quotient.mkₐ_ker R _).ge
    rw [← map_comp] at h
    intro x hx
    have hx' := (hopfIdealLocus_le_ker_iff (g.comp f) N).2 h hx
    rwa [RingHom.mem_ker, AlgHom.comp_apply, Ideal.Quotient.mkₐ_eq_mk,
      Ideal.Quotient.eq_zero_iff_mem] at hx'

end Module.Grassmannian
