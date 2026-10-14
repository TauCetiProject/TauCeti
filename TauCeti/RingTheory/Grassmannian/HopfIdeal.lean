/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import Mathlib.RingTheory.HopfAlgebra.Quotient
public import Mathlib.RingTheory.HopfAlgebra.TensorProduct
public import TauCeti.RingTheory.FittingIdeal.Content
public import TauCeti.RingTheory.Grassmannian.Basic

/-!
# The closed locus of Hopf ideals in the Grassmannian

Let `H` be a Hopf algebra over a commutative ring `R`. A point of the Grassmannian functor
`A ↦ G(k, A ⊗[R] H; A)` is an `A`-submodule `N` of `A ⊗[R] H` whose quotient is finite projective
of constant rank `k`. When `N` is a Hopf ideal, the quotient is a Hopf algebra over `A`, so for
commutative `H` the closed subscheme `Spec ((A ⊗[R] H) ⧸ N)` is a subgroup scheme of the base change
of `Spec H` to `A`, finite locally free of rank `k` over `A`. This file shows that being a Hopf
ideal is a closed condition on the Grassmannian: there is an ideal `N.hopfIdealLocus` of `A` such
that, for every `R`-algebra map `f : A → B`, the base change of `N` to `B` is a Hopf ideal of
`B ⊗[R] H` exactly when `f` kills `N.hopfIdealLocus`
(`Module.Grassmannian.hopfIdealLocus_le_ker_iff`). The formation of the ideal commutes with base
change (`Module.Grassmannian.hopfIdealLocus_map`). This is the input for cutting out, inside the
Grassmannian scheme, the closed subscheme which parametrises the subgroup schemes of rank `k`.

The ideal is the sum of four contents, one for each Hopf-ideal condition. Write
`π : A ⊗[R] H → Q` for the quotient by `N`. The image of `N` under the counit, under `π ∘ S` for
the antipode `S`, under `(π ⊗ π) ∘ Δ` for the comultiplication `Δ`, and under
`π ∘ (1 ⊗ₜ h) * -` for each `h : H` is a submodule of a finite projective `A`-module (`A`, `Q`,
`Q ⊗[A] Q` and `Q`), and its content (`Submodule.minorsIdeal 1`) is the ideal along which it
vanishes after base change (`IsBaseChange.minorsIdeal_one_le_ker_iff`). The comparison of the
four conditions after base change with the base change of the four maps is
`Module.Grassmannian.ker_baseChangeMkQ_le_ker_iff_minorsIdeal_le`, which holds for any module
in place of `H`.

## Main definitions

* `Module.Grassmannian.hopfIdealLocus N`: the ideal of `A` cutting out the locus where `N` is a
  Hopf ideal.

## Main results

* `Module.Grassmannian.ker_baseChangeMkQ_le_ker_iff_minorsIdeal_le`: a linear condition on the
  base change of a point of the Grassmannian, which is the base change of a condition on the
  point, is cut out by a content ideal.
* `Module.Grassmannian.hopfIdealLocus_le_ker_iff`: the base change of `N` along `f` is a Hopf
  ideal exactly when `f` kills `N.hopfIdealLocus`.
* `Module.Grassmannian.hopfIdealLocus_eq_bot_iff`: `N` itself is a Hopf ideal exactly when
  `N.hopfIdealLocus = ⊥`.
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

section ClosedCondition

variable {M : Type v} [AddCommGroup M] [Module R M] [Algebra A B] [IsScalarTower R A B]

/-- **Closed conditions on the base change of a submodule.** Let `N ≤ A ⊗[R] M` and let `Φ` be a
`B`-linear map out of `B ⊗[R] M` which, on the image of `A ⊗[R] M`, is the base change `g ∘ Ψ` of
an `A`-linear map `Ψ` to a projective module `X`. Then `Φ` vanishes on the kernel of
`baseChangeMkQ B N`, the base change of `N` to `B`, exactly when `A → B` kills the content of
`Ψ(N)`. -/
theorem ker_baseChangeMkQ_le_ker_iff_minorsIdeal_le (N : Submodule A (A ⊗[R] M))
    {X Y : Type*} [AddCommGroup X] [Module A X] [Module.Projective A X] [AddCommGroup Y]
    [Module B Y] [Module A Y] [IsScalarTower A B Y] (Φ : B ⊗[R] M →ₗ[B] Y)
    (Ψ : A ⊗[R] M →ₗ[A] X) {g : X →ₗ[A] Y} (hg : IsBaseChange B g)
    (hΦ : ∀ x, Φ ((IsScalarTower.toAlgHom R A B).toLinearMap.rTensor M x) = g (Ψ x)) :
    LinearMap.ker (baseChangeMkQ B N) ≤ LinearMap.ker Φ ↔
      (N.map Ψ).minorsIdeal 1 ≤ RingHom.ker (algebraMap A B) := by
  simp [ker_baseChangeMkQ_le_ker_iff, hΦ, hg.minorsIdeal_one_le_ker_iff]

end ClosedCondition

variable {H : Type v} [Ring H] [HopfAlgebra R H]

/-- The **locus of Hopf ideals**: for a point `N` of the Grassmannian of rank-`k` quotients of
`A ⊗[R] H`, the ideal of `A` killed by an `R`-algebra map `f : A → B` exactly when the base change
of `N` to `B` is a Hopf ideal of `B ⊗[R] H` (`Module.Grassmannian.hopfIdealLocus_le_ker_iff`).

With `π : A ⊗[R] H → Q` the quotient by `N`, it is the sum of the contents of the images of `N`
under the counit, under `π ∘ S` for the antipode `S`, under `(π ⊗ π) ∘ Δ` for the
comultiplication `Δ`, and under `π ∘ (1 ⊗ₜ h) * -` for all `h : H`. -/
noncomputable def hopfIdealLocus (N : G(k, A ⊗[R] H; A)) : Ideal A :=
  (N.toSubmodule.map (Coalgebra.counit (R := A) (A := A ⊗[R] H))).minorsIdeal 1 ⊔
    (N.toSubmodule.map (N.toSubmodule.mkQ ∘ₗ HopfAlgebra.antipode A)).minorsIdeal 1 ⊔
    (N.toSubmodule.map (TensorProduct.map N.toSubmodule.mkQ N.toSubmodule.mkQ ∘ₗ
      Coalgebra.comul (R := A))).minorsIdeal 1 ⊔
    ⨆ h : H, (N.toSubmodule.map
      (N.toSubmodule.mkQ ∘ₗ LinearMap.mulLeft A ((1 : A) ⊗ₜ[R] h))).minorsIdeal 1

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
      have ha : a ⊗ₜ[R] h₂ = a • ((1 : A) ⊗ₜ[R] h₂) := by rw [smul_tmul', smul_eq_mul, mul_one]
      simp only [map_tmul, baseChangeMkQ_tmul, AlgebraTensorModule.tensorTensorTensorComm_tmul,
        Submodule.mkQ_apply, AlgebraTensorModule.distribBaseChange_tmul]
      rw [ha, Submodule.Quotient.mk_smul, tmul_smul, smul_tmul', Algebra.smul_def, mul_one]
    | add s t hs ht => simp only [tmul_add, map_add, hs, ht]
  | add x y hx hy => simp only [map_add, tmul_add, hx, hy]

/-- The four summands of `hopfIdealLocus` are killed by `A → B` exactly when the counit, the
antipode, the comultiplication and the multiplications by the `1 ⊗ₜ h` are compatible with the base
change of `N` to `B`. -/
private theorem hopfIdealLocus_le_ker_algebraMap_iff_ker_le (N : G(k, A ⊗[R] H; A)) :
    N.hopfIdealLocus ≤ RingHom.ker (algebraMap A B) ↔
      ((LinearMap.ker (baseChangeMkQ B N.toSubmodule) ≤
          LinearMap.ker (Coalgebra.counit (R := B) (A := B ⊗[R] H)) ∧
        LinearMap.ker (baseChangeMkQ B N.toSubmodule) ≤
          LinearMap.ker (baseChangeMkQ B N.toSubmodule ∘ₗ HopfAlgebra.antipode B)) ∧
        LinearMap.ker (baseChangeMkQ B N.toSubmodule) ≤
          LinearMap.ker (TensorProduct.map (baseChangeMkQ B N.toSubmodule)
            (baseChangeMkQ B N.toSubmodule) ∘ₗ Coalgebra.comul (R := B))) ∧
        ∀ h : H, LinearMap.ker (baseChangeMkQ B N.toSubmodule) ≤
          LinearMap.ker
            (baseChangeMkQ B N.toSubmodule ∘ₗ LinearMap.mulLeft B ((1 : B) ⊗ₜ[R] h)) := by
  set Q := A ⊗[R] H ⧸ N.toSubmodule
  set π := baseChangeMkQ B N.toSubmodule
  have hgQ := TensorProduct.isBaseChange A Q B
  have hcounit := ker_baseChangeMkQ_le_ker_iff_minorsIdeal_le N.toSubmodule
    (Coalgebra.counit (R := B) (A := B ⊗[R] H)) (Coalgebra.counit (R := A) (A := A ⊗[R] H))
    (IsBaseChange.linearMap A B) fun x ↦ by
      induction x using TensorProduct.inductionOn with
      | tmul a h => simp [Algebra.smul_def, ← IsScalarTower.algebraMap_apply]
      | add x y hx hy => simp only [map_add, hx, hy]
  have hantipode := ker_baseChangeMkQ_le_ker_iff_minorsIdeal_le N.toSubmodule
    (π ∘ₗ HopfAlgebra.antipode B) (N.toSubmodule.mkQ ∘ₗ HopfAlgebra.antipode A) hgQ fun x ↦ by
      have hS : HopfAlgebra.antipode B ((IsScalarTower.toAlgHom R A B).toLinearMap.rTensor H x) =
          (IsScalarTower.toAlgHom R A B).toLinearMap.rTensor H (HopfAlgebra.antipode A x) := by
        induction x using TensorProduct.inductionOn with
        | tmul a h => simp
        | add x y hx hy => simp only [map_add, hx, hy]
      rw [LinearMap.comp_apply, hS, baseChangeMkQ_rTensor, LinearMap.comp_apply,
        TensorProduct.mk_apply]
  let g : Q ⊗[A] Q →ₗ[A] (B ⊗[A] Q) ⊗[B] (B ⊗[A] Q) :=
    (AlgebraTensorModule.distribBaseChange A B Q Q).toLinearMap.restrictScalars A ∘ₗ
      TensorProduct.mk A B (Q ⊗[A] Q) 1
  have hg : IsBaseChange B g :=
    IsBaseChange.of_equiv (AlgebraTensorModule.distribBaseChange A B Q Q) fun _ ↦ rfl
  -- the module types are given explicitly to keep elaboration from unfolding the tensor products
  have hcomul := ker_baseChangeMkQ_le_ker_iff_minorsIdeal_le (X := Q ⊗[A] Q)
    (Y := (B ⊗[A] Q) ⊗[B] (B ⊗[A] Q)) N.toSubmodule
    (TensorProduct.map π π ∘ₗ Coalgebra.comul (R := B))
    (TensorProduct.map N.toSubmodule.mkQ N.toSubmodule.mkQ ∘ₗ Coalgebra.comul (R := A)) hg
    fun x ↦ by
      rw [LinearMap.comp_apply, map_baseChangeMkQ_comul_rTensor, LinearMap.comp_apply]
      rfl
  have hmul (h : H) := ker_baseChangeMkQ_le_ker_iff_minorsIdeal_le N.toSubmodule
    (π ∘ₗ LinearMap.mulLeft B ((1 : B) ⊗ₜ[R] h))
    (N.toSubmodule.mkQ ∘ₗ LinearMap.mulLeft A ((1 : A) ⊗ₜ[R] h)) hgQ fun x ↦ by
      have hm : ((1 : B) ⊗ₜ[R] h) * (IsScalarTower.toAlgHom R A B).toLinearMap.rTensor H x =
          (IsScalarTower.toAlgHom R A B).toLinearMap.rTensor H (((1 : A) ⊗ₜ[R] h) * x) := by
        induction x using TensorProduct.inductionOn with
        | tmul a h' => simp
        | add x y hx hy => simp only [mul_add, map_add, hx, hy]
      rw [LinearMap.comp_apply, LinearMap.mulLeft_apply, hm, baseChangeMkQ_rTensor,
        LinearMap.comp_apply, TensorProduct.mk_apply, LinearMap.mulLeft_apply]
  simp only [hopfIdealLocus, sup_le_iff, iSup_le_iff, ← hcounit, ← hantipode, ← hcomul, ← hmul]
  -- the two sides differ only in the abbreviation `π`
  rfl

/-- The universal property of `hopfIdealLocus`, for an algebra `B` over `A`. -/
private theorem hopfIdealLocus_le_ker_algebraMap_iff (N : G(k, A ⊗[R] H; A)) :
    N.hopfIdealLocus ≤ RingHom.ker (algebraMap A B) ↔
      ∃ I : Ideal (B ⊗[R] H), I.restrictScalars B = LinearMap.ker (baseChangeMkQ B N.toSubmodule) ∧
        I.IsHopfIdeal B := by
  set π := baseChangeMkQ B N.toSubmodule
  set K := LinearMap.ker π
  -- `π` is the quotient map by `K` followed by an isomorphism, so `K` is a coideal exactly when
  -- `(π ⊗ π) ∘ Δ` vanishes on it
  let e := π.quotKerEquivOfSurjective (baseChangeMkQ_surjective N.toSubmodule)
  have hmap (t : (B ⊗[R] H) ⊗[B] (B ⊗[R] H)) :
      TensorProduct.map π π t = TensorProduct.congr e e (TensorProduct.map K.mkQ K.mkQ t) := by
    rw [← LinearEquiv.coe_toLinearMap, TensorProduct.congr, LinearEquiv.toLinearMap_ofLinearMap,
      ← LinearMap.comp_apply, ← TensorProduct.map_comp]
    rfl
  have hcoideal : K.IsCoideal ↔ K ≤ LinearMap.ker (Coalgebra.counit (R := B)) ∧
      K ≤ LinearMap.ker (TensorProduct.map π π ∘ₗ Coalgebra.comul (R := B)) := by
    simp only [Submodule.isCoideal_iff, IsConcreteLE.le_iff, LinearMap.mem_ker,
      LinearMap.comp_apply, hmap, LinearEquiv.map_eq_zero_iff]
  rw [hopfIdealLocus_le_ker_algebraMap_iff_ker_le]
  constructor
  · rintro ⟨⟨⟨hε, hS⟩, hΔ⟩, hμ⟩
    -- `K` is an ideal, since `B ⊗[R] H` is spanned over `B` by the `1 ⊗ₜ h`
    have hmulK (c : B ⊗[R] H) {y : B ⊗[R] H} (hy : y ∈ K) : c * y ∈ K := by
      induction c using TensorProduct.inductionOn with
      | tmul b h =>
        rw [show b ⊗ₜ[R] h = b • ((1 : B) ⊗ₜ[R] h) by rw [smul_tmul', smul_eq_mul, mul_one],
          smul_mul_assoc]
        exact K.smul_mem b (hμ h hy)
      | add c d hc hd =>
        rw [add_mul]
        exact K.add_mem hc hd
    let I : Ideal (B ⊗[R] H) := { K.toAddSubmonoid with smul_mem' := fun c _ hy ↦ hmulK c hy }
    -- `I` is `K` with the larger scalar ring, so the two have the same underlying set
    have hI : I.restrictScalars B = K := rfl
    exact ⟨I, hI, { toIsCoideal := hI ▸ hcoideal.2 ⟨hε, hΔ⟩, antipode_mem := fun _ hy ↦ hS hy }⟩
  · rintro ⟨I, hI, hHopf⟩
    have hmem (y : B ⊗[R] H) : y ∈ K ↔ y ∈ I := by rw [← hI, Submodule.restrictScalars_mem]
    obtain ⟨hε, hΔ⟩ := hcoideal.1 (hI ▸ hHopf.toIsCoideal)
    refine ⟨⟨⟨hε, fun y hy ↦ ?_⟩, hΔ⟩, fun h y hy ↦ ?_⟩
    · exact (hmem _).2 (hHopf.antipode_mem ((hmem y).1 hy))
    · exact (hmem _).2 (I.mul_mem_left _ ((hmem y).1 hy))

end BaseChange

/-- **Being a Hopf ideal is a closed condition on the Grassmannian.** For a point `N` of
`G(k, A ⊗[R] H; A)` and an `R`-algebra map `f : A → B`, the base change of `N` to `B` is a Hopf
ideal of `B ⊗[R] H` exactly when `f` kills `N.hopfIdealLocus`. -/
theorem hopfIdealLocus_le_ker_iff (f : A →ₐ[R] B) (N : G(k, A ⊗[R] H; A)) :
    N.hopfIdealLocus ≤ RingHom.ker f ↔
      ∃ I : Ideal (B ⊗[R] H), I.restrictScalars B = (map f N).toSubmodule ∧ I.IsHopfIdeal B := by
  algebraize [f.toRingHom]
  -- `algebraize` makes `f` the structure map of `B` as an `A`-algebra
  have hf : IsScalarTower.toAlgHom R A B = f := AlgHom.ext fun _ ↦ rfl
  rw [← hf, map_toAlgHom_toSubmodule]
  exact hopfIdealLocus_le_ker_algebraMap_iff N

/-- A point `N` of `G(k, A ⊗[R] H; A)` is a Hopf ideal of `A ⊗[R] H` exactly when
`N.hopfIdealLocus` vanishes. -/
theorem hopfIdealLocus_eq_bot_iff (N : G(k, A ⊗[R] H; A)) :
    N.hopfIdealLocus = ⊥ ↔
      ∃ I : Ideal (A ⊗[R] H), I.restrictScalars A = N.toSubmodule ∧ I.IsHopfIdeal A := by
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
