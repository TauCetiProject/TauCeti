/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.Algebra.Bialgebra.Module.TensorProduct
public import Mathlib.Algebra.Module.BigOperators
public import TauCeti.Algebra.HopfAlgebra.InverseAntipode

/-!
# The internal Hom of modules over a Hopf algebra

Let `H` be a Hopf algebra over a commutative semiring `R` whose antipode `S` is bijective. For two
`H`-modules `M` and `N`, the `R`-linear maps `M → N` form an `H`-module under Qi's action

  `(h • f)(m) = ∑ h₂ • f(S⁻¹(h₁) • m)`,

where `∑ h₁ ⊗ h₂` is the coproduct of `h`. With this action, `Hom_R(M, -)` is right adjoint to the
coproduct tensor product `M ⊗ -`: an `H`-linear map `M ⊗ X → N` is the same as an `H`-linear map
`X → Hom_R(M, N)`. The fixed points of the action, the `f` with `h • f = ε(h) f`, are exactly the
`H`-linear maps.

This is the internal Hom of the monoidal category of all `H`-modules. For finite-dimensional `M`
its action is that of `*M ⊗ N`, for the left dual `*M` through `S⁻¹`; the formula
`∑ h₁ • f(S(h₂) • m)` is the action of `N ⊗ M*` through the right dual, a different module structure
on the same space, and is not used.

`AlgHom.hopfLinHom` is the action on linear maps between two representations, built from the
coproduct and the two commuting actions by pre- and postcomposition. For modules,
`TauCeti.BialgebraModule.LinHom` is a type synonym of `M →ₗ[R] N` carrying this action, with
`linHomEquiv` identifying it with the native type of linear maps.

## Main declarations

* `AlgHom.hopfLinHom`: the representation of `H` on linear maps between two representations.
* `TauCeti.BialgebraModule.LinHom`: linear maps with Qi's action.
* `TauCeti.BialgebraModule.linHomEquiv_smul_apply_eq_sum`: the action in a representation of the
  coproduct.
* `TauCeti.BialgebraModule.linHomEval`: evaluation `M ⊗ Hom_R(M, N) → N`, which is `H`-linear.
* `TauCeti.BialgebraModule.linHomCoeval`: the map `X → Hom_R(M, M ⊗ X)`, `x ↦ (m ↦ m ⊗ x)`, which is
  `H`-linear.
* `TauCeti.BialgebraModule.linHomPostcomp`: postcomposition with an `H`-linear map.
* `TauCeti.BialgebraModule.tensorLinHomEquiv`: the tensor-Hom adjunction
  `Hom_H(M ⊗ X, N) ≃ Hom_H(X, Hom_R(M, N))`.
* `TauCeti.BialgebraModule.forall_smul_eq_counit_smul_iff`: the fixed points of the action are the
  `H`-linear maps.

## References

* Y. Qi, *Hopfological algebra*, Compos. Math. 150 (2014), Lemma 2.3 and Definition 5.1.
* C. Kassel, *Quantum Groups*, Chapter III, for duals of modules over Hopf algebras.

The construction follows Mathlib's `Representation.linHom` and the closed structure on `Rep`,
with the coproduct and the inverse antipode in place of the group inverse.
-/

public noncomputable section

open scoped TensorProduct
open Coalgebra TauCeti.HopfAlgebra

namespace AlgHom

variable {R H V W : Type*} [CommSemiring R] [Semiring H] [HopfAlgebra R H]
  [AddCommMonoid V] [Module R V] [AddCommMonoid W] [Module R W]

/-- Precomposition with the inverse antipode action, `a • f = f ∘ ρ(S⁻¹(a))`. -/
private def hopfLinHomPre (ρ : H →ₐ[R] Module.End R V)
    (hS : Function.Bijective (HopfAlgebra.antipode R : H →ₗ[R] H)) :
    H →ₐ[R] Module.End R (V →ₗ[R] W) :=
  .ofLinearMap ((LinearMap.llcomp R V V W).flip.comp (ρ.toLinearMap.comp (inverseAntipode hS)))
    (by ext f v; simp [inverseAntipode_one])
    (fun a b => by ext f v; simp [inverseAntipode_mul])

/-- Postcomposition with an action, `a • f = σ(a) ∘ f`. -/
private def hopfLinHomPost (σ : H →ₐ[R] Module.End R W) :
    H →ₐ[R] Module.End R (V →ₗ[R] W) :=
  .ofLinearMap ((LinearMap.llcomp R V W W).comp σ.toLinearMap)
    (by ext f v; simp)
    (fun a b => by ext f v; simp)

/-- The representation of a Hopf algebra with bijective antipode on linear maps between two
representations, `(a f)(v) = ∑ σ(a₂) (f (ρ(S⁻¹(a₁)) v))`. -/
def hopfLinHom (ρ : H →ₐ[R] Module.End R V) (σ : H →ₐ[R] Module.End R W)
    (hS : Function.Bijective (HopfAlgebra.antipode R : H →ₗ[R] H)) :
    H →ₐ[R] Module.End R (V →ₗ[R] W) :=
  (Algebra.TensorProduct.lift (hopfLinHomPre ρ hS) (hopfLinHomPost σ)
    (fun _ _ => LinearMap.ext fun _ => rfl)).comp (Bialgebra.comulAlgHom R H)

/-- The action on linear maps, in any finite representation of the coproduct. -/
theorem hopfLinHom_apply_eq_sum (ρ : H →ₐ[R] Module.End R V) (σ : H →ₐ[R] Module.End R W)
    (hS : Function.Bijective (HopfAlgebra.antipode R : H →ₗ[R] H)) {a : H} {ι : Type*}
    (𝓡 : Repr R a ι) (f : V →ₗ[R] W) :
    ρ.hopfLinHom σ hS a f =
      ∑ i ∈ 𝓡.index, σ (𝓡.right i) ∘ₗ f ∘ₗ ρ (inverseAntipode hS (𝓡.left i)) := by
  rw [hopfLinHom, coe_comp, Function.comp_apply, Bialgebra.comulAlgHom_apply, ← 𝓡.eq, map_sum,
    LinearMap.sum_apply]
  refine Finset.sum_congr rfl fun i _ => ?_
  ext v
  simp [hopfLinHomPre, hopfLinHomPost]

/-- A group-like element acts on linear maps by conjugation. -/
theorem hopfLinHom_apply_of_comul_eq_tmul (ρ : H →ₐ[R] Module.End R V)
    (σ : H →ₐ[R] Module.End R W) (hS : Function.Bijective (HopfAlgebra.antipode R : H →ₗ[R] H))
    {a : H} (ha : comul (R := R) a = a ⊗ₜ[R] a) (f : V →ₗ[R] W) :
    ρ.hopfLinHom σ hS a f = σ a ∘ₗ f ∘ₗ ρ (inverseAntipode hS a) := by
  simpa using ρ.hopfLinHom_apply_eq_sum σ hS ⟨{()}, fun _ => a, fun _ => a, by simp [ha]⟩ f

/-- A primitive element acts on linear maps by the sum of post- and precomposition. -/
theorem hopfLinHom_apply_of_comul_eq_add (ρ : H →ₐ[R] Module.End R V)
    (σ : H →ₐ[R] Module.End R W) (hS : Function.Bijective (HopfAlgebra.antipode R : H →ₗ[R] H))
    {a : H} (ha : comul (R := R) a = a ⊗ₜ[R] 1 + 1 ⊗ₜ[R] a) (f : V →ₗ[R] W) :
    ρ.hopfLinHom σ hS a f = f ∘ₗ ρ (inverseAntipode hS a) + σ a ∘ₗ f := by
  have := ρ.hopfLinHom_apply_eq_sum σ hS (a := a)
    ⟨Finset.univ, ![a, 1], ![1, a], by simp [ha, Fin.sum_univ_two]⟩ f
  simpa [Fin.sum_univ_two, inverseAntipode_one, Module.End.one_eq_id] using this

end AlgHom

namespace TauCeti.BialgebraModule

/-- The `R`-linear maps between two modules over a Hopf algebra `H` with bijective antipode, with
a separate carrier for Qi's action `(h • f)(m) = ∑ h₂ • f(S⁻¹(h₁) • m)`.

As for `Dual` and `LeftDual`, the synonym keeps the `H`-action apart from other actions on the
native type of linear maps, the base action is restriction of the `H`-action along the algebra
map, and `linHomEquiv` identifies it with the native type. -/
def LinHom (R H M N : Type*) [CommSemiring R] [Semiring H] [HopfAlgebra R H]
    [AddCommMonoid M] [Module R M] [AddCommMonoid N] [Module R N]
    (_hS : Function.Bijective (HopfAlgebra.antipode R : H →ₗ[R] H)) :=
  M →ₗ[R] N

section Defs

variable (R H M N : Type*) [CommSemiring R] [Semiring H] [HopfAlgebra R H]
  (hS : Function.Bijective (HopfAlgebra.antipode R : H →ₗ[R] H))

instance [AddCommMonoid M] [Module R M] [AddCommMonoid N] [Module R N] :
    AddCommMonoid (LinHom R H M N hS) :=
  inferInstanceAs (AddCommMonoid (M →ₗ[R] N))

instance [AddCommMonoid M] [Module R M] [AddCommGroup N] [Module R N] :
    AddCommGroup (LinHom R H M N hS) :=
  inferInstanceAs (AddCommGroup (M →ₗ[R] N))

variable [AddCommMonoid M] [Module R M] [Module H M] [IsScalarTower R H M]
  [AddCommMonoid N] [Module R N] [Module H N] [IsScalarTower R H N]

/-- Qi's module structure on the carrier of linear maps. -/
@[no_expose] noncomputable instance : Module H (LinHom R H M N hS) :=
  Module.compHom (M →ₗ[R] N)
    ((Algebra.lsmul R R M).hopfLinHom (Algebra.lsmul R R N) hS).toRingHom

/-- The base action is restriction of Qi's action along the algebra map.
The priority keeps this presentation ahead of generic natural and integer scalar actions. -/
noncomputable instance (priority := 1100) : Module R (LinHom R H M N hS) :=
  Module.compHom (LinHom R H M N hS) (algebraMap R H)

/-- Qi's module is compatible with its base scalar action. -/
instance : IsScalarTower R H (LinHom R H M N hS) :=
  IsScalarTower.of_compHom R H (LinHom R H M N hS)

/-- The underlying `R`-linear identification with the native type of linear maps. -/
noncomputable def linHomEquiv : LinHom R H M N hS ≃ₗ[R] (M →ₗ[R] N) :=
  let e : LinHom R H M N hS ≃+ (M →ₗ[R] N) := AddEquiv.refl _
  e.toLinearEquiv fun r f =>
    LinearMap.congr_fun
      (((Algebra.lsmul R R M).hopfLinHom (Algebra.lsmul R R N) hS).commutes r) f

end Defs

variable {R H M X N N' : Type*} [CommSemiring R] [Semiring H] [HopfAlgebra R H]
  [AddCommMonoid M] [Module R M] [Module H M] [IsScalarTower R H M]
  [AddCommMonoid N] [Module R N] [Module H N] [IsScalarTower R H N]
  [AddCommMonoid N'] [Module R N'] [Module H N'] [IsScalarTower R H N']
  [AddCommMonoid X] [Module R X] [Module H X] [IsScalarTower R H X]
  {hS : Function.Bijective (HopfAlgebra.antipode R : H →ₗ[R] H)}

/-- Two elements of the internal Hom agree if their underlying linear maps agree pointwise. -/
@[ext]
theorem LinHom.ext {f g : LinHom R H M N hS}
    (h : ∀ m, linHomEquiv R H M N hS f m = linHomEquiv R H M N hS g m) : f = g :=
  (linHomEquiv R H M N hS).injective (LinearMap.ext h)

/-- Under the identification with linear maps, `H` acts through `AlgHom.hopfLinHom`. -/
theorem linHomEquiv_smul (h : H) (f : LinHom R H M N hS) :
    linHomEquiv R H M N hS (h • f) =
      (Algebra.lsmul R R M).hopfLinHom (Algebra.lsmul R R N) hS h (linHomEquiv R H M N hS f) :=
  (rfl)

/-- Qi's action in any finite representation `∑ᵢ h₁ᵢ ⊗ h₂ᵢ` of the coproduct of `h`:
`(h • f)(m) = ∑ᵢ h₂ᵢ • f(S⁻¹(h₁ᵢ) • m)`. -/
theorem linHomEquiv_smul_apply_eq_sum {h : H} {ι : Type*} (𝓡 : Repr R h ι)
    (f : LinHom R H M N hS) (m : M) :
    linHomEquiv R H M N hS (h • f) m =
      ∑ i ∈ 𝓡.index, 𝓡.right i • linHomEquiv R H M N hS f (inverseAntipode hS (𝓡.left i) • m) := by
  simp [linHomEquiv_smul, AlgHom.hopfLinHom_apply_eq_sum _ _ hS 𝓡]

/-- A group-like element acts by conjugation, `(g • f)(m) = g • f(S⁻¹(g) • m)`. -/
theorem linHomEquiv_smul_apply_of_comul_eq_tmul {g : H} (hg : comul (R := R) g = g ⊗ₜ[R] g)
    (f : LinHom R H M N hS) (m : M) :
    linHomEquiv R H M N hS (g • f) m =
      g • linHomEquiv R H M N hS f (inverseAntipode hS g • m) := by
  simpa using linHomEquiv_smul_apply_eq_sum ⟨{()}, fun _ => g, fun _ => g, by simp [hg]⟩ f m

/-- A primitive element acts by `(d • f)(m) = f(S⁻¹(d) • m) + d • f(m)`; when `S⁻¹(d) = -d`
this is the commutator of `f` with the action of `d`. -/
theorem linHomEquiv_smul_apply_of_comul_eq_add {d : H}
    (hd : comul (R := R) d = d ⊗ₜ[R] 1 + 1 ⊗ₜ[R] d) (f : LinHom R H M N hS) (m : M) :
    linHomEquiv R H M N hS (d • f) m =
      linHomEquiv R H M N hS f (inverseAntipode hS d • m) + d • linHomEquiv R H M N hS f m := by
  have := linHomEquiv_smul_apply_eq_sum (hS := hS) (h := d)
    ⟨Finset.univ, ![d, 1], ![1, d], by simp [hd, Fin.sum_univ_two]⟩ f m
  simpa [Fin.sum_univ_two, inverseAntipode_one] using this

/-! ### Evaluation -/

variable (R H M N hS) in
/-- Evaluation `m ⊗ f ↦ f m`, as an `R`-linear map. -/
private noncomputable def linHomEvalAux : Tensor R H M (LinHom R H M N hS) →ₗ[R] N :=
  TensorProduct.lift (linHomEquiv R H M N hS).toLinearMap.flip ∘ₗ
    (tensorEquiv R H M (LinHom R H M N hS)).toLinearMap

private theorem linHomEvalAux_tmul (m : M) (f : LinHom R H M N hS) :
    linHomEvalAux R H M N hS (tmul R H m f) = linHomEquiv R H M N hS f m := by
  simp [linHomEvalAux]

private theorem linHomEvalAux_smul_tmul (h : H) (m : M) (f : LinHom R H M N hS) :
    linHomEvalAux R H M N hS (h • tmul R H m f) = h • linHomEquiv R H M N hS f m := by
  let 𝓡 := Repr.arbitrary R h
  -- `Θ (a ⊗ b ⊗ c) = c • f(S⁻¹(b) • a • m)`. Applied to the two sides of coassociativity, it
  -- gives the evaluation of `h • (m ⊗ f)` and, after cancelling `∑ S⁻¹(a₂) a₁ = ε(a)`, `h • f m`.
  let F : H →ₗ[R] N :=
    linHomEquiv R H M N hS f ∘ₗ (LinearMap.toSpanSingleton H M m).restrictScalars R
  let G : H ⊗[R] H →ₗ[R] H := LinearMap.mul' R H ∘ₗ (inverseAntipode hS).rTensor H ∘ₗ
    (TensorProduct.comm R H H).toLinearMap
  let Θ : H ⊗[R] (H ⊗[R] H) →ₗ[R] N :=
    TensorProduct.lift ((Algebra.lsmul R R N).toLinearMap.flip ∘ₗ F) ∘ₗ
      TensorProduct.map G LinearMap.id ∘ₗ (TensorProduct.assoc R H H H).symm.toLinearMap
  have hΘ (a b c : H) :
      Θ (a ⊗ₜ (b ⊗ₜ c)) = c • linHomEquiv R H M N hS f (inverseAntipode hS b • a • m) := by
    simp [Θ, G, F, mul_smul]
  have key := congrArg Θ (sum_tmul_tmul_eq 𝓡 (fun i => Repr.arbitrary R (𝓡.left i))
    (fun i => Repr.arbitrary R (𝓡.right i)))
  simp only [map_sum, hΘ] at key
  have hl : ∀ x ∈ 𝓡.index, ∑ j ∈ (Repr.arbitrary R (𝓡.left x)).index, 𝓡.right x •
      linHomEquiv R H M N hS f (inverseAntipode hS ((Repr.arbitrary R (𝓡.left x)).right j) •
        (Repr.arbitrary R (𝓡.left x)).left j • m) =
      counit (R := R) (𝓡.left x) • 𝓡.right x • linHomEquiv R H M N hS f m := by
    intro x _
    simp_rw [← Finset.smul_sum, smul_smul, ← map_sum, ← Finset.sum_smul,
      sum_inverseAntipode_mul_eq_algebraMap_counit, algebraMap_smul, map_smul,
      smul_comm (𝓡.right x)]
  rw [Finset.sum_congr rfl hl] at key
  simp_rw [← smul_assoc, ← Finset.sum_smul, sum_counit_smul] at key
  rw [key, smul_tmul_eq_sum 𝓡, map_sum]
  refine Finset.sum_congr rfl fun x _ => ?_
  rw [linHomEvalAux_tmul, linHomEquiv_smul_apply_eq_sum (Repr.arbitrary R (𝓡.right x))]
  simp only [smul_assoc]

private theorem linHomEvalAux_smul (h : H) (x : Tensor R H M (LinHom R H M N hS)) :
    linHomEvalAux R H M N hS (h • x) = h • linHomEvalAux R H M N hS x := by
  induction x using Tensor.inductionOn with
  | htmul m f => rw [linHomEvalAux_smul_tmul, linHomEvalAux_tmul]
  | hadd x y hx hy => rw [smul_add, map_add, map_add, hx, hy, smul_add]

variable (R H M N hS) in
/-- Evaluation `M ⊗ Hom_R(M, N) → N`, `m ⊗ f ↦ f m`. It is `H`-linear for the coproduct action on
the tensor product and Qi's action on linear maps. -/
noncomputable def linHomEval : Tensor R H M (LinHom R H M N hS) →ₗ[H] N where
  __ := linHomEvalAux R H M N hS
  map_smul' := linHomEvalAux_smul

/-- Evaluation applies the linear map to the element. -/
@[simp]
theorem linHomEval_tmul (m : M) (f : LinHom R H M N hS) :
    linHomEval R H M N hS (tmul R H m f) = linHomEquiv R H M N hS f m :=
  linHomEvalAux_tmul m f

/-! ### Coevaluation -/

variable (R H M X hS) in
/-- The map `x ↦ (m ↦ m ⊗ x)`, as an `R`-linear map. -/
private noncomputable def linHomCoevalAux : X →ₗ[R] LinHom R H M (Tensor R H M X) hS :=
  (linHomEquiv R H M (Tensor R H M X) hS).symm.toLinearMap ∘ₗ
    LinearMap.llcomp R M (M ⊗[R] X) (Tensor R H M X) (tensorEquiv R H M X).symm.toLinearMap ∘ₗ
      (TensorProduct.mk R M X).flip

private theorem linHomCoevalAux_apply (x : X) (m : M) :
    linHomEquiv R H M (Tensor R H M X) hS (linHomCoevalAux R H M X hS x) m = tmul R H m x := by
  simp [linHomCoevalAux]

private theorem linHomCoevalAux_smul (h : H) (x : X) :
    linHomCoevalAux R H M X hS (h • x) = h • linHomCoevalAux R H M X hS x := by
  ext m
  let 𝓡 := Repr.arbitrary R h
  -- `Θ (a ⊗ b ⊗ c) = (b • S⁻¹(a) • m) ⊗ (c • x)`. Applied to the two sides of coassociativity,
  -- it gives, after cancelling `∑ a₂ S⁻¹(a₁) = ε(a)`, `m ⊗ h • x` and `(h • coeval x)(m)`.
  let G : H ⊗[R] H →ₗ[R] H :=
    LinearMap.mul' R H ∘ₗ (TensorProduct.comm R H H).toLinearMap ∘ₗ (inverseAntipode hS).rTensor H
  let Θ : H ⊗[R] (H ⊗[R] H) →ₗ[R] M ⊗[R] X :=
    TensorProduct.map ((LinearMap.toSpanSingleton H M m).restrictScalars R ∘ₗ G)
      ((LinearMap.toSpanSingleton H X x).restrictScalars R) ∘ₗ
      (TensorProduct.assoc R H H H).symm.toLinearMap
  have hΘ (a b c : H) : Θ (a ⊗ₜ (b ⊗ₜ c)) = (b • inverseAntipode hS a • m) ⊗ₜ (c • x) := by
    simp [Θ, G, mul_smul]
  have key := congrArg Θ (sum_tmul_tmul_eq 𝓡 (fun i => Repr.arbitrary R (𝓡.left i))
    (fun i => Repr.arbitrary R (𝓡.right i)))
  simp only [map_sum, hΘ] at key
  simp_rw [smul_smul, ← TensorProduct.sum_tmul, ← Finset.sum_smul,
    sum_mul_inverseAntipode_eq_algebraMap_counit, algebraMap_smul, TensorProduct.smul_tmul,
    ← TensorProduct.tmul_sum, ← smul_assoc, ← Finset.sum_smul, sum_counit_smul] at key
  rw [linHomCoevalAux_apply, linHomEquiv_smul_apply_eq_sum 𝓡]
  apply (tensorEquiv R H M X).injective
  rw [tensorEquiv_tmul, key, map_sum]
  refine Finset.sum_congr rfl fun i _ => ?_
  rw [linHomCoevalAux_apply, smul_tmul_eq_sum (Repr.arbitrary R (𝓡.right i)), map_sum]
  simp only [tensorEquiv_tmul, smul_smul]

variable (R H M X hS) in
/-- Coevaluation `X → Hom_R(M, M ⊗ X)`, `x ↦ (m ↦ m ⊗ x)`. It is `H`-linear for Qi's action on
linear maps and the coproduct action on the tensor product. -/
noncomputable def linHomCoeval : X →ₗ[H] LinHom R H M (Tensor R H M X) hS where
  __ := linHomCoevalAux R H M X hS
  map_smul' := linHomCoevalAux_smul

/-- Coevaluation sends `x` to the linear map `m ↦ m ⊗ x`. -/
@[simp]
theorem linHomEquiv_linHomCoeval_apply (x : X) (m : M) :
    linHomEquiv R H M (Tensor R H M X) hS (linHomCoeval R H M X hS x) m = tmul R H m x :=
  linHomCoevalAux_apply x m

/-! ### Postcomposition -/

variable (M hS) in
/-- Postcomposition with an `H`-linear map `g : N → N'`, as an `H`-linear map
`Hom_R(M, N) → Hom_R(M, N')`. -/
noncomputable def linHomPostcomp (g : N →ₗ[H] N') : LinHom R H M N hS →ₗ[H] LinHom R H M N' hS where
  toFun f := (linHomEquiv R H M N' hS).symm
    ((g.restrictScalars R).comp (linHomEquiv R H M N hS f))
  map_add' f f' := by ext; simp
  map_smul' h f := by
    ext m
    simp [linHomEquiv_smul_apply_eq_sum (Repr.arbitrary R h)]

/-- Postcomposition applies the `H`-linear map after the linear map. -/
@[simp]
theorem linHomEquiv_linHomPostcomp_apply (g : N →ₗ[H] N') (f : LinHom R H M N hS) (m : M) :
    linHomEquiv R H M N' hS (linHomPostcomp M hS g f) m = g (linHomEquiv R H M N hS f m) := by
  simp [linHomPostcomp]

/-- Postcomposition with the identity is the identity. -/
@[simp]
theorem linHomPostcomp_id : linHomPostcomp M hS (LinearMap.id : N →ₗ[H] N) = LinearMap.id := by
  ext; simp

/-- Postcomposition is functorial. -/
theorem linHomPostcomp_comp {N'' : Type*} [AddCommMonoid N''] [Module R N''] [Module H N'']
    [IsScalarTower R H N''] (g : N →ₗ[H] N') (g' : N' →ₗ[H] N'') :
    linHomPostcomp M hS (g' ∘ₗ g) = linHomPostcomp M hS g' ∘ₗ linHomPostcomp M hS g := by
  ext; simp

/-! ### The tensor-Hom adjunction -/

variable (R H M X N hS) in
/-- The tensor-Hom adjunction for modules over a Hopf algebra with bijective antipode: `H`-linear
maps `M ⊗ X → N` correspond to `H`-linear maps `X → Hom_R(M, N)` by currying,
`g ↦ (x ↦ (m ↦ g (m ⊗ x)))`. -/
noncomputable def tensorLinHomEquiv :
    (Tensor R H M X →ₗ[H] N) ≃ₗ[R] (X →ₗ[H] LinHom R H M N hS) where
  toFun g := linHomPostcomp M hS g ∘ₗ linHomCoeval R H M X hS
  invFun φ := linHomEval R H M N hS ∘ₗ tensorMap R H LinearMap.id φ
  map_add' g g' := by ext; simp
  map_smul' r g := by ext; simp
  left_inv g := by ext; simp
  right_inv φ := by ext; simp

/-- Currying evaluates on pure tensors. -/
@[simp]
theorem linHomEquiv_tensorLinHomEquiv_apply (g : Tensor R H M X →ₗ[H] N) (x : X) (m : M) :
    linHomEquiv R H M N hS (tensorLinHomEquiv R H M X N hS g x) m = g (tmul R H m x) := by
  simp [tensorLinHomEquiv]

/-- Uncurrying evaluates the image of the second factor on the first. -/
@[simp]
theorem tensorLinHomEquiv_symm_apply_tmul (φ : X →ₗ[H] LinHom R H M N hS) (m : M) (x : X) :
    (tensorLinHomEquiv R H M X N hS).symm φ (tmul R H m x) = linHomEquiv R H M N hS (φ x) m := by
  simp [tensorLinHomEquiv]

/-! ### Invariants -/

/-- The fixed points of Qi's action are the `H`-linear maps: `h • f = ε(h) f` for every `h`
exactly when `f (h • m) = h • f m` for every `h` and `m`. -/
theorem forall_smul_eq_counit_smul_iff (f : LinHom R H M N hS) :
    (∀ h : H, h • f = counit (R := R) h • f) ↔
      ∀ (h : H) (m : M), linHomEquiv R H M N hS f (h • m) = h • linHomEquiv R H M N hS f m := by
  constructor
  · intro hf h m
    let 𝓡 := Repr.arbitrary R h
    have hsum : ∑ i ∈ 𝓡.index, counit (R := R) (𝓡.right i) • 𝓡.left i = h := by
      have := congrArg (TensorProduct.rid R H) (sum_tmul_counit_eq 𝓡)
      simpa only [map_sum, TensorProduct.rid_tmul, one_smul] using this
    -- Evaluation is `H`-linear, so `h • f m` is `∑ (h₂ • f)(h₁ • m) = ∑ ε(h₂) f(h₁ • m)`.
    symm
    calc h • linHomEquiv R H M N hS f m = linHomEval R H M N hS (h • tmul R H m f) := by
          rw [map_smul, linHomEval_tmul]
      _ = ∑ i ∈ 𝓡.index,
            counit (R := R) (𝓡.right i) • linHomEquiv R H M N hS f (𝓡.left i • m) := by
          simp [smul_tmul_eq_sum 𝓡, hf]
      _ = linHomEquiv R H M N hS f (h • m) := by
          conv_rhs => rw [← hsum, Finset.sum_smul, map_sum]
          simp [smul_assoc]
  · intro hf h
    ext m
    rw [linHomEquiv_smul_apply_eq_sum (Repr.arbitrary R h), map_smul, LinearMap.smul_apply]
    simp_rw [← hf, smul_smul, ← map_sum, ← Finset.sum_smul,
      sum_mul_inverseAntipode_eq_algebraMap_counit, algebraMap_smul, map_smul]

end TauCeti.BialgebraModule
