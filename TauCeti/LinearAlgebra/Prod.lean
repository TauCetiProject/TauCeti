/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import Mathlib.Analysis.Complex.Basic
public import Mathlib.LinearAlgebra.Determinant
public import Mathlib.LinearAlgebra.Basis.Prod
public import Mathlib.LinearAlgebra.Prod

/-!
# Product linear maps

Mathlib builds the product `e₁.prodCongr e₂` of two linear equivalences, acting on `M₁ × M₂`
componentwise. This file identifies which automorphisms of `M₁ × M₂` arise this way, records the
determinants of such a product and of a block triangular `skewProd` automorphism, and records
that scalar multiplication on a product of complex modules is the product map of the two scalar
multiplications.

The characterization needs only containment: an automorphism `g` of `M₁ × M₂` that maps
`M₁ × 0` into `M₁ × 0` and `0 × M₂` into `0 × M₂` already acts componentwise, and each component
is then bijective because `g` is. No finiteness is used, so no separate hypothesis on `g⁻¹` is
needed. This is what identifies the image of the orthogonal group of an orthogonal sum of
quadratic forms with the subgroup preserving both summands.

## Main results

* `LinearEquiv.prodCongr_inj`: products of linear equivalences are equal exactly when their
  factors are.
* `LinearEquiv.exists_prodCongr_eq_iff`: an automorphism of `M₁ × M₂` is `e₁.prodCongr e₂` for
  automorphisms `e₁` of `M₁` and `e₂` of `M₂` exactly when it maps each factor into itself.
* `LinearEquiv.det_prodCongr`: `det (e₁.prodCongr e₂) = det e₁ * det e₂` for finite free
  modules; this is `LinearMap.det_prodMap` for linear equivalences.
* `Module.Basis.det_prod`: changes between product bases have the product determinant.
* `Module.Basis.map_prodAssoc_prod`: reassociating a triple product carries the ordered product
  basis `(b × c) × d` to `b × (c × d)`, up to relabelling the index.
* `LinearEquiv.det_skewProd`: the same determinant formula for block triangular
  automorphisms, independently of the off-diagonal block.
* `LinearEquiv.nonempty_linearEquiv_of_isUnit_snd_comp_inr`: a linear equivalence `M × P ≃ N × P`
  whose lower-right block is invertible gives `M ≃ N`.
* `LinearMap.finrank_graph`: the graph of a linear map `M → M₂` has the dimension of `M`.
* `TauCeti.LinearMap.lsmul_restrictScalars_prodMap`: multiplication by a scalar on a product of
  complex modules is the product map of the two multiplications.
-/

public section

namespace LinearEquiv

section Semiring

variable {R M₁ M₂ : Type*} [Semiring R] [AddCommMonoid M₁] [Module R M₁] [AddCommMonoid M₂]
  [Module R M₂]

/-- Products of linear equivalences are equal exactly when their factors are. -/
@[simp]
theorem prodCongr_inj {M₃ M₄ : Type*} [AddCommMonoid M₃] [Module R M₃] [AddCommMonoid M₄]
    [Module R M₄] {e₁ e₁' : M₁ ≃ₗ[R] M₃} {e₂ e₂' : M₂ ≃ₗ[R] M₄} :
    e₁.prodCongr e₂ = e₁'.prodCongr e₂' ↔ e₁ = e₁' ∧ e₂ = e₂' := by
  refine ⟨fun h ↦ ⟨ext fun m ↦ ?_, ext fun m ↦ ?_⟩, fun ⟨h₁, h₂⟩ ↦ h₁ ▸ h₂ ▸ rfl⟩
  · simpa using congrArg Prod.fst (DFunLike.congr_fun h (m, 0))
  · simpa using congrArg Prod.snd (DFunLike.congr_fun h (0, m))

/-- A linear automorphism of `M₁ × M₂` is a product `e₁.prodCongr e₂` of automorphisms of the
factors exactly when it maps `M₁ × 0` into `M₁ × 0` and `0 × M₂` into `0 × M₂`. -/
theorem exists_prodCongr_eq_iff {g : (M₁ × M₂) ≃ₗ[R] M₁ × M₂} :
    (∃ (e₁ : M₁ ≃ₗ[R] M₁) (e₂ : M₂ ≃ₗ[R] M₂), e₁.prodCongr e₂ = g) ↔
      (∀ m₁, (g (m₁, 0)).2 = 0) ∧ ∀ m₂, (g (0, m₂)).1 = 0 := by
  refine ⟨?_, fun ⟨h₁, h₂⟩ ↦ ?_⟩
  · rintro ⟨e₁, e₂, rfl⟩
    exact ⟨fun _ ↦ by simp, fun _ ↦ by simp⟩
  -- Preserving both factors makes `g` act componentwise.
  have hg (x : M₁ × M₂) : g x = ((g (x.1, 0)).1, (g (0, x.2)).2) := by
    conv_lhs => rw [← Prod.fst_add_snd x, map_add]
    ext <;> simp [h₁, h₂]
  have hb₁ : Function.Bijective
      (LinearMap.fst R M₁ M₂ ∘ₗ g.toLinearMap ∘ₗ LinearMap.inl R M₁ M₂) := by
    refine ⟨fun a b hab ↦ ?_, fun y ↦ ⟨(g.symm (y, 0)).1, ?_⟩⟩
    · have : g (a, 0) = g (b, 0) := Prod.ext hab (by rw [h₁, h₁])
      simpa using g.injective this
    · simpa using (congrArg Prod.fst (hg (g.symm (y, 0)))).symm
  have hb₂ : Function.Bijective
      (LinearMap.snd R M₁ M₂ ∘ₗ g.toLinearMap ∘ₗ LinearMap.inr R M₁ M₂) := by
    refine ⟨fun a b hab ↦ ?_, fun y ↦ ⟨(g.symm (0, y)).2, ?_⟩⟩
    · have : g (0, a) = g (0, b) := Prod.ext (by rw [h₂, h₂]) hab
      simpa using g.injective this
    · simpa using (congrArg Prod.snd (hg (g.symm (0, y)))).symm
  refine ⟨ofBijective _ hb₁, ofBijective _ hb₂, ?_⟩
  ext x <;> simp [hg x]

end Semiring

section CommRing

variable {R M₁ M₂ : Type*} [CommRing R] [AddCommGroup M₁] [Module R M₁] [AddCommGroup M₂]
  [Module R M₂] [Module.Free R M₁] [Module.Finite R M₁] [Module.Free R M₂] [Module.Finite R M₂]

/-- The determinant of a product of linear automorphisms of finite free modules is the product of
their determinants. -/
@[simp]
theorem det_prodCongr (e₁ : M₁ ≃ₗ[R] M₁) (e₂ : M₂ ≃ₗ[R] M₂) :
    (e₁.prodCongr e₂).det = e₁.det * e₂.det := by
  ext
  simp [coe_det, LinearMap.det_prodMap]

/-- The determinant of a block triangular linear automorphism is the product of the
determinants of its diagonal blocks. -/
@[simp]
theorem det_skewProd (e₁ : M₁ ≃ₗ[R] M₁) (e₂ : M₂ ≃ₗ[R] M₂) (f : M₁ →ₗ[R] M₂) :
    (e₁.skewProd e₂ f).det = e₁.det * e₂.det := by
  classical
  let b₁ := Module.Free.chooseBasis R M₁
  let b₂ := Module.Free.chooseBasis R M₂
  have hmat : LinearMap.toMatrix (b₁.prod b₂) (b₁.prod b₂)
      (e₁.skewProd e₂ f).toLinearMap =
      Matrix.fromBlocks (LinearMap.toMatrix b₁ b₁ e₁.toLinearMap) 0
        (LinearMap.toMatrix b₁ b₂ f) (LinearMap.toMatrix b₂ b₂ e₂.toLinearMap) := by
    ext i j
    cases i <;> cases j <;>
      simp [LinearMap.toMatrix_apply, LinearEquiv.skewProd_apply]
  apply Units.ext
  simp only [coe_det, Units.val_mul]
  rw [← LinearMap.det_toMatrix (b₁.prod b₂), hmat, Matrix.det_fromBlocks_zero₁₂,
    LinearMap.det_toMatrix, LinearMap.det_toMatrix]

end CommRing

section Cancellation

variable {A : Type*} [Semiring A] {M N : Type*} [AddCommMonoid M] [Module A M]
  [AddCommMonoid N] [Module A N] {P : Type*} [AddCommGroup P] [Module A P]

/-- **Cancellation from an invertible lower-right block.** A linear equivalence `M × P ≃ N × P`
whose lower-right block `P → P` is invertible induces a linear equivalence `M ≃ N`. -/
theorem nonempty_linearEquiv_of_isUnit_snd_comp_inr (e₁ : (M × P) ≃ₗ[A] (N × P))
    (he₁ : IsUnit ((LinearMap.snd A N P).comp
      ((e₁ : (M × P) →ₗ[A] (N × P)).comp (LinearMap.inr A M P)))) :
    Nonempty (M ≃ₗ[A] N) := by
  -- Clear the lower-left block. The resulting triangular equivalence restricts to an
  -- equivalence on pairs with second coordinate zero, so no subtraction in `M` or `N` is needed.
  let c₁ : M →ₗ[A] P := (LinearMap.snd A N P).comp
    ((e₁ : (M × P) →ₗ[A] (N × P)).comp (LinearMap.inl A M P))
  let d₁ : Module.End A P := (LinearMap.snd A N P).comp
    ((e₁ : (M × P) →ₗ[A] (N × P)).comp (LinearMap.inr A M P))
  let ed : P ≃ₗ[A] P := LinearEquiv.ofBijective d₁ ((Module.End.isUnit_iff d₁).mp he₁)
  let sourceShear : (M × P) ≃ₗ[A] (M × P) :=
    (LinearEquiv.refl A M).skewProd (LinearEquiv.refl A P)
      (-((ed.symm : P →ₗ[A] P).comp c₁))
  let triangular := sourceShear.trans e₁
  let s : M →ₗ[A] N := (LinearMap.fst A N P).comp
    ((triangular : (M × P) →ₗ[A] (N × P)).comp (LinearMap.inl A M P))
  have he₁_snd (m : M) (p : P) : (e₁ (m, p)).2 = c₁ m + d₁ p := by
    rw [← Prod.fst_add_snd (m, p), map_add]
    rfl
  have htriangular (m : M) (p : P) : (triangular (m, p)).2 = d₁ p := by
    simp only [triangular, sourceShear, LinearEquiv.trans_apply,
      LinearEquiv.skewProd_apply, LinearEquiv.refl_apply, LinearMap.neg_apply,
      LinearMap.comp_apply]
    rw [he₁_snd]
    have hd_inv (x : P) : d₁ (ed.symm x) = x := ed.apply_symm_apply x
    simp [hd_inv]
  have hs_injective : Function.Injective s := by
    intro m m' hmm'
    have hpair : triangular (m, 0) = triangular (m', 0) := by
      apply Prod.ext
      · exact hmm'
      · rw [htriangular, htriangular]
    exact congrArg Prod.fst (triangular.injective hpair)
  have hs_surjective : Function.Surjective s := by
    intro n
    obtain ⟨⟨m, p⟩, hmp⟩ := triangular.surjective (n, 0)
    have hp : d₁ p = 0 := by simpa only [htriangular] using congrArg Prod.snd hmp
    have hp : p = 0 := ed.injective (hp.trans ed.map_zero.symm)
    subst p
    exact ⟨m, congrArg Prod.fst hmp⟩
  exact ⟨LinearEquiv.ofBijective s ⟨hs_injective, hs_surjective⟩⟩

end Cancellation

end LinearEquiv

namespace LinearMap

/-- The graph of a linear map `f : M → M₂` has the dimension of `M`. -/
theorem finrank_graph {R M M₂ : Type*} [Ring R] [AddCommGroup M] [Module R M] [AddCommGroup M₂]
    [Module R M₂] (f : M →ₗ[R] M₂) : Module.finrank R (graph f) = Module.finrank R M := by
  rw [graph_eq_range_prod, finrank_range_of_inj]
  intro x y h
  exact congr(($h).1)

end LinearMap

namespace Module.Basis

variable {R E F ι κ : Type*} [CommRing R] [AddCommGroup E] [Module R E]
  [AddCommGroup F] [Module R F] [Fintype ι] [DecidableEq ι] [Fintype κ] [DecidableEq κ]

/-- The determinant of a change between product bases is the product of the two factor
change-of-basis determinants. -/
theorem det_prod (b b' : Basis ι R E) (c c' : Basis κ R F) :
    (b.prod c).det (b'.prod c') = b.det b' * c.det c' := by
  rw [Basis.det_apply, Basis.det_apply, Basis.det_apply]
  have he : (b.prod c).toMatrix (b'.prod c') =
      Matrix.fromBlocks (b.toMatrix b') 0 0 (c.toMatrix c') := by
    ext i j
    cases i <;> cases j <;>
      simp [Basis.toMatrix_apply]
  rw [he, Matrix.det_fromBlocks_zero₂₁]

/-- Reassociating `(E × F) × G` as `E × (F × G)` carries the ordered product basis `(b × c) × d`,
indexed by `Fin (m + n + p)`, to the ordered product basis `b × (c × d)`, reindexed along
`m + n + p = m + (n + p)`. -/
theorem map_prodAssoc_prod {R E F G : Type*} [Semiring R] [AddCommMonoid E] [Module R E]
    [AddCommMonoid F] [Module R F] [AddCommMonoid G] [Module R G] {m n p : ℕ}
    (b : Basis (Fin m) R E) (c : Basis (Fin n) R F) (d : Basis (Fin p) R G) :
    ((((b.prod c).reindex finSumFinEquiv).prod d).reindex finSumFinEquiv).map
        (LinearEquiv.prodAssoc R E F G) =
      ((b.prod ((c.prod d).reindex finSumFinEquiv)).reindex finSumFinEquiv).reindex
        (finCongr (add_assoc m n p).symm) := by
  refine Basis.eq_of_apply_eq fun i ↦ ?_
  induction i using Fin.addCases with
  | left j =>
    induction j using Fin.addCases with
    | left k =>
      have h : Fin.cast (add_assoc m n p) (Fin.castAdd p (Fin.castAdd n k)) =
          Fin.castAdd (n + p) k := Fin.ext rfl
      simp [Basis.prod_apply, h]
    | right k =>
      have h : Fin.cast (add_assoc m n p) (Fin.castAdd p (Fin.natAdd m k)) =
          Fin.natAdd m (Fin.castAdd p k) := Fin.ext rfl
      simp [Basis.prod_apply, h]
  | right k =>
    have h : Fin.cast (add_assoc m n p) (Fin.natAdd (m + n) k) =
        Fin.natAdd m (Fin.natAdd n k) := Fin.ext (Nat.add_assoc m n k)
    simp [Basis.prod_apply, h]

end Module.Basis

namespace TauCeti

namespace LinearMap

variable {E E' : Type*} [AddCommGroup E] [Module ℝ E] [Module ℂ E] [IsScalarTower ℝ ℂ E]
  [AddCommGroup E'] [Module ℝ E'] [Module ℂ E'] [IsScalarTower ℝ ℂ E']

/-- **Multiplication by a scalar on a product of complex modules is carried out blockwise.** Read
as a real-linear map, multiplication by `c` on `E × E'` is the `LinearMap.prodMap` of the
multiplications by `c` on the two factors. -/
theorem lsmul_restrictScalars_prodMap (c : ℂ) :
    (LinearMap.lsmul ℂ (E × E') c).restrictScalars ℝ =
      LinearMap.prodMap ((LinearMap.lsmul ℂ E c).restrictScalars ℝ)
        ((LinearMap.lsmul ℂ E' c).restrictScalars ℝ) := by
  apply LinearMap.ext (R := ℝ)
  intro x
  rcases x with ⟨x, y⟩
  simp [LinearMap.lsmul_apply, LinearMap.prodMap_apply]

end LinearMap

end TauCeti
