/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import Mathlib.LinearAlgebra.Dual.Lemmas
public import Mathlib.LinearAlgebra.GeneralLinearGroup.Basic
public import Mathlib.RingTheory.HopfAlgebra.Convolution
public import TauCeti.Algebra.Bialgebra.Module.TensorProduct
public import TauCeti.LinearAlgebra.Coevaluation

/-!
# Contragredient Hopf algebra representations

For a representation `ρ : H →ₐ[R] Module.End R V`, its contragredient acts on the native
module dual by `(a φ)(v) = φ(ρ(S(a))v)`. Transposition reverses composition, so the antipode's
antimultiplicativity makes this an algebra representation. Transposing an intertwiner gives
an intertwiner in the reverse direction.

The ordinary evaluation map into the double dual intertwines the action twisted by `S²`.
If `S²(a) = g a g⁻¹` for a unit `g`, evaluation after `ρ(g)` instead intertwines the original
action. On a reflexive module this is a natural linear equivalence with the double
contragredient. In particular it supplies the underlying maps of the pivotal comparison
for finite-dimensional Hopf modules; tensor compatibility requires additional group-like data.

For modules rather than representations, `TauCeti.BialgebraModule.Dual` is a type synonym of the
native dual carrying this contragredient action. Ordinary contraction `dualEval` and, over a
field, the finite-dimensional coevaluation `dualCoeval` are `H`-linear for the coproduct tensor
product `BialgebraModule.Tensor` and the counit module `BialgebraModule.Trivial`, by the two
antipode identities.

The construction uses Mathlib's `Module.Dual.transpose`, `Module.evalEquiv` and
`LinearMap.GeneralLinearGroup.generalLinearEquiv`. The dual and double-dual conventions are those of
Kassel, *Quantum Groups*, Chapter XIV.
-/

public noncomputable section

open Module HopfAlgebra

namespace AlgHom

variable {R H V : Type*} [CommSemiring R] [Semiring H] [HopfAlgebra R H]
  [AddCommMonoid V] [Module R V]

/-- The contragredient representation, with action through the antipode on the argument
of a linear functional. -/
def hopfDual (ρ : H →ₐ[R] Module.End R V) : H →ₐ[R] Module.End R (Dual R V) :=
  .ofLinearMap (Dual.transpose.comp (ρ.toLinearMap.comp (antipode R)))
    (by ext φ v; simp [Dual.transpose_apply])
    (fun a b => by
      ext φ v
      simp [Dual.transpose_apply, antipode_mul_antidistrib, Module.End.mul_apply])

/-- The contragredient action on a functional is precomposition with the antipode action. -/
@[simp]
theorem hopfDual_apply (ρ : H →ₐ[R] Module.End R V) (a : H) (φ : Dual R V) (v : V) :
    ρ.hopfDual a φ v = φ (ρ (antipode R a) v) := (rfl)

/-- Evaluation into the double contragredient intertwines the action twisted by `S²`. -/
theorem hopfDual_hopfDual_eval (ρ : H →ₐ[R] Module.End R V) (a : H) (v : V) :
    ρ.hopfDual.hopfDual a (Dual.eval R V v) =
      Dual.eval R V (ρ (antipode R (antipode R a)) v) := by
  ext φ
  simp

variable [Module.IsReflexive R V]

/-- Evaluation after the action of a unit. When the unit implements the square of the
antipode, this is the intertwining equivalence with the double contragredient. -/
def unitEvalEquiv (ρ : H →ₐ[R] Module.End R V) (g : Hˣ) :
    V ≃ₗ[R] Dual R (Dual R V) :=
  (LinearMap.GeneralLinearGroup.generalLinearEquiv R V (Units.map ρ.toMonoidHom g)).trans
    (Module.evalEquiv R V)

/-- The double-dual comparison sends `v` to the functional `φ ↦ φ(gv)`. -/
@[simp]
theorem unitEvalEquiv_apply (ρ : H →ₐ[R] Module.End R V) (g : Hˣ) (v : V)
    (φ : Dual R V) : ρ.unitEvalEquiv g v φ = φ (ρ (g : H) v) := (rfl)

/-- The inverse comparison evaluates the double functional, then acts by `g⁻¹`. -/
@[simp]
theorem unitEvalEquiv_symm_apply (ρ : H →ₐ[R] Module.End R V) (g : Hˣ)
    (Φ : Dual R (Dual R V)) :
    (ρ.unitEvalEquiv g).symm Φ = ρ (↑g⁻¹ : H) ((Module.evalEquiv R V).symm Φ) := (rfl)

/-- If `g` implements `S²`, the double-dual comparison intertwines the original action
with the double contragredient. -/
theorem unitEvalEquiv_intertwines (ρ : H →ₐ[R] Module.End R V) (g : Hˣ)
    (hg : ∀ a : H, antipode R (antipode R a) = (g : H) * a * ↑g⁻¹)
    (a : H) (v : V) :
    ρ.unitEvalEquiv g (ρ a v) = ρ.hopfDual.hopfDual a (ρ.unitEvalEquiv g v) := by
  have hcancel : ρ (↑g⁻¹ : H) (ρ (g : H) v) = v := by
    rw [← Module.End.mul_apply, ← map_mul]
    simp
  ext φ
  simp [hg, Module.End.mul_apply, hcancel]

end AlgHom

namespace LinearMap

variable {R H V W : Type*} [CommSemiring R] [Semiring H] [HopfAlgebra R H]
  [AddCommMonoid V] [Module R V] [AddCommMonoid W] [Module R W]
  {ρ : H →ₐ[R] Module.End R V} {σ : H →ₐ[R] Module.End R W}

/-- The transpose of an intertwiner intertwines the contragredients in the reverse direction. -/
theorem hopfDual_intertwines (f : V →ₗ[R] W)
    (hf : ∀ (a : H) (v : V), f (ρ a v) = σ a (f v)) (a : H) (φ : Dual R W) :
    f.dualMap (σ.hopfDual a φ) = ρ.hopfDual a (f.dualMap φ) := by
  ext v
  simp [hf]

variable [Module.IsReflexive R V] [Module.IsReflexive R W]

/-- Evaluation after a fixed unit is natural in intertwining maps. -/
theorem unitEvalEquiv_natural (f : V →ₗ[R] W)
    (hf : ∀ (a : H) (v : V), f (ρ a v) = σ a (f v)) (g : Hˣ) (v : V) :
    f.dualMap.dualMap (ρ.unitEvalEquiv g v) = σ.unitEvalEquiv g (f v) := by
  ext φ
  simp [hf]

end LinearMap

namespace TauCeti.BialgebraModule

open scoped TensorProduct

/-- The linear dual over `R`, with a separate carrier for the contragredient action
`(a φ)(m) = φ(S(a) m)` of a Hopf algebra `H`.

As for `Tensor`, the synonym keeps the `H`-action apart from other actions on the native dual,
the base action is restriction of the `H`-action along the algebra map, and `dualEquiv`
identifies it with the native dual. -/
def Dual (R _H M : Type*) [CommSemiring R] [AddCommMonoid M] [Module R M] := Module.Dual R M

variable (R H M : Type*) [CommSemiring R] [AddCommMonoid M] [Module R M]

instance : AddCommMonoid (Dual R H M) := inferInstanceAs (AddCommMonoid (Module.Dual R M))

instance (R H M : Type*) [CommRing R] [AddCommGroup M] [Module R M] :
    AddCommGroup (Dual R H M) :=
  inferInstanceAs (AddCommGroup (Module.Dual R M))

section Action

variable [Semiring H] [HopfAlgebra R H] [Module H M] [IsScalarTower R H M]

/-- The contragredient module structure on the dual carrier. -/
@[no_expose] noncomputable instance : Module H (Dual R H M) :=
  Module.compHom (Module.Dual R M) (Algebra.lsmul R R M).hopfDual.toRingHom

/-- The base action is restriction of the contragredient action along the algebra map.
The priority keeps this presentation ahead of generic natural and integer scalar actions. -/
noncomputable instance (priority := 1100) : Module R (Dual R H M) :=
  Module.compHom (Dual R H M) (algebraMap R H)

/-- The contragredient module is compatible with its base scalar action. -/
instance : IsScalarTower R H (Dual R H M) := IsScalarTower.of_compHom R H (Dual R H M)

/-- The underlying `R`-linear identification with the native dual. -/
noncomputable def dualEquiv : Dual R H M ≃ₗ[R] Module.Dual R M :=
  let e : Dual R H M ≃+ Module.Dual R M := AddEquiv.refl _
  e.toLinearEquiv fun r φ => LinearMap.congr_fun ((Algebra.lsmul R R M).hopfDual.commutes r) φ

/-- An element of `H` acts on a functional by precomposition with the action of its
antipode. -/
@[simp]
theorem dualEquiv_smul_apply (h : H) (φ : Dual R H M) (m : M) :
    dualEquiv R H M (h • φ) m = dualEquiv R H M φ (HopfAlgebra.antipode R h • m) := (rfl)

/-- The dual of a finite projective module is finite. -/
instance [Module.Projective R M] [Module.Finite R M] : Module.Finite R (Dual R H M) :=
  Module.Finite.equiv (dualEquiv R H M).symm

end Action

section Evaluation

variable [Semiring H] [HopfAlgebra R H] [Module H M] [IsScalarTower R H M]

/-- On a pure tensor, the action of `t : H ⊗ H` followed by contraction is contraction after
`mul' ((S ⊗ 1) t)` acts on the vector. -/
private theorem contractLeft_tensorPairAction (t : H ⊗[R] H) (φ : Dual R H M) (m : M) :
    contractLeft R M (TensorProduct.map (dualEquiv R H M).toLinearMap LinearMap.id
        (tensorPairAction R H (Dual R H M) M t (φ ⊗ₜ[R] m))) =
      dualEquiv R H M φ
        (LinearMap.mul' R H ((HopfAlgebra.antipode R).rTensor H t) • m) := by
  induction t using TensorProduct.inductionOn with
  | add t u ht hu => simp only [map_add, LinearMap.add_apply, ht, hu, add_smul]
  | tmul a b => simp [mul_smul]

/-- The underlying `R`-linear contraction of the dual against the module. -/
private noncomputable def dualEvalAux : Tensor R H (Dual R H M) M →ₗ[R] Trivial R H :=
  (trivialEquiv R H).symm.toLinearMap ∘ₗ contractLeft R M ∘ₗ
    TensorProduct.map (dualEquiv R H M).toLinearMap LinearMap.id ∘ₗ
      (tensorEquiv R H (Dual R H M) M).toLinearMap

private theorem dualEvalAux_tmul (φ : Dual R H M) (m : M) :
    dualEvalAux R H M (tmul R H φ m) = (trivialEquiv R H).symm (dualEquiv R H M φ m) := by
  simp [dualEvalAux]

private theorem dualEvalAux_smul (h : H) (x : Tensor R H (Dual R H M) M) :
    dualEvalAux R H M (h • x) = h • dualEvalAux R H M x := by
  induction x using Tensor.inductionOn with
  | hadd x y hx hy => simp only [smul_add, map_add, hx, hy]
  | htmul φ m =>
    apply (trivialEquiv R H).injective
    have := contractLeft_tensorPairAction R H M (Coalgebra.comul h) φ m
    simp only [HopfAlgebra.mul_antipode_rTensor_comul_apply, algebraMap_smul,
      LinearMap.map_smul_of_tower] at this
    simpa [dualEvalAux, tensorAction_apply, dualEvalAux_tmul] using this

/-- Contraction of the contragredient against the module, `φ ⊗ m ↦ φ m`. It is `H`-linear for
the coproduct action by the antipode identity `S(h₁) h₂ = ε(h) 1`. -/
noncomputable def dualEval : Tensor R H (Dual R H M) M →ₗ[H] Trivial R H where
  __ := dualEvalAux R H M
  map_smul' := dualEvalAux_smul R H M

/-- Evaluation applies the functional to the vector. -/
@[simp]
theorem dualEval_tmul (φ : Dual R H M) (m : M) :
    dualEval R H M (tmul R H φ m) = (trivialEquiv R H).symm (dualEquiv R H M φ m) :=
  dualEvalAux_tmul R H M φ m

end Evaluation

section Coevaluation

variable (k : Type*) [Field k] (H : Type*) [Semiring H] [HopfAlgebra k H]
variable (V : Type*) [AddCommGroup V] [Module k V] [Module H V] [IsScalarTower k H V]
  [FiniteDimensional k V]

/-- The canonical tensor `∑ i, b i ⊗ b^i` in the coproduct tensor product with the
contragredient. -/
private noncomputable def coevalVec : Tensor k H V (Dual k H V) :=
  (tensorEquiv k H V (Dual k H V)).symm
    (TensorProduct.map LinearMap.id (dualEquiv k H V).symm.toLinearMap (coevaluation k V 1))

omit [FiniteDimensional k V] in
/-- A pure element `a ⊗ b` of `H ⊗ H` acts on the image of the native tensor product with the
dual by `a` on vectors and by the transpose of the action of `S(b)` on functionals. -/
private theorem tensorPairAction_map_dualEquiv_symm (a b : H)
    (y : V ⊗[k] Module.Dual k V) :
    tensorPairAction k H V (Dual k H V) (a ⊗ₜ[k] b)
        (TensorProduct.map LinearMap.id (dualEquiv k H V).symm.toLinearMap y) =
      TensorProduct.map LinearMap.id (dualEquiv k H V).symm.toLinearMap
        (TensorProduct.map (Algebra.lsmul k k V a)
          (Algebra.lsmul k k V (HopfAlgebra.antipode k b)).dualMap y) := by
  induction y using TensorProduct.inductionOn with
  | add y z hy hz => simp only [map_add, hy, hz]
  | tmul v ψ =>
    have hψ : b • (dualEquiv k H V).symm ψ =
        (dualEquiv k H V).symm ((Algebra.lsmul k k V (HopfAlgebra.antipode k b)).dualMap ψ) :=
      (dualEquiv k H V).injective (LinearMap.ext fun w => by simp)
    simp [hψ]

/-- The canonical tensor is invariant: `H` acts on it through the counit. -/
private theorem smul_coevalVec (h : H) :
    h • coevalVec k H V = Coalgebra.counit (R := k) h • coevalVec k H V := by
  -- Under the native identification, the action of `t : H ⊗ H` on the canonical tensor is the
  -- action of `mul' ((1 ⊗ S) t)` on its vector factor, by dinaturality of coevaluation.
  have key (t : H ⊗[k] H) :
      tensorPairAction k H V (Dual k H V) t
          (TensorProduct.map LinearMap.id (dualEquiv k H V).symm.toLinearMap
            (coevaluation k V 1)) =
        TensorProduct.map LinearMap.id (dualEquiv k H V).symm.toLinearMap
          ((Algebra.lsmul k k V
            (LinearMap.mul' k H ((HopfAlgebra.antipode k).lTensor H t))).rTensor _
              (coevaluation k V 1)) := by
    induction t using TensorProduct.inductionOn with
    | add t u ht hu => simp only [map_add, LinearMap.add_apply, ht, hu, LinearMap.rTensor_add]
    | tmul a b =>
      have hdin := LinearMap.congr_fun
        (LinearMap.rTensor_comp_coevaluation (Algebra.lsmul k k V (HopfAlgebra.antipode k b))) 1
      rw [LinearMap.comp_apply, LinearMap.comp_apply] at hdin
      rw [tensorPairAction_map_dualEquiv_symm]
      congr 1
      rw [← LinearMap.rTensor_comp_lTensor, LinearMap.comp_apply, ← hdin,
        ← LinearMap.rTensor_comp_apply]
      simp [map_mul, Module.End.mul_eq_comp]
  apply (tensorEquiv k H V (Dual k H V)).injective
  simp [coevalVec, tensorAction_apply, key, Module.algebraMap_end_eq_smul_id]

/-- The underlying `k`-linear coevaluation into the coproduct tensor product with the
contragredient. -/
private noncomputable def dualCoevalAux : Trivial k H →ₗ[k] Tensor k H V (Dual k H V) :=
  (LinearMap.toSpanSingleton k _ (coevalVec k H V)) ∘ₗ (trivialEquiv k H).toLinearMap

private theorem dualCoevalAux_apply (r : Trivial k H) :
    dualCoevalAux k H V r = trivialEquiv k H r • coevalVec k H V := (rfl)

private theorem dualCoevalAux_smul (h : H) (r : Trivial k H) :
    dualCoevalAux k H V (h • r) = h • dualCoevalAux k H V r := by
  rw [dualCoevalAux_apply, dualCoevalAux_apply, trivialEquiv_smul, smul_comm h, smul_coevalVec,
    smul_smul, mul_comm]

/-- The finite-dimensional coevaluation `r ↦ r ∑ i, b i ⊗ b^i` into the coproduct tensor
product with the contragredient. It is `H`-linear by the antipode identity `h₁ S(h₂) = ε(h) 1`
and dinaturality of coevaluation. -/
noncomputable def dualCoeval : Trivial k H →ₗ[H] Tensor k H V (Dual k H V) where
  __ := dualCoevalAux k H V
  map_smul' := dualCoevalAux_smul k H V

/-- Coevaluation is the native coevaluation, under the identification of the coproduct tensor
product and the contragredient with their native counterparts. -/
theorem dualCoeval_apply (r : Trivial k H) :
    dualCoeval k H V r =
      (tensorEquiv k H V (Dual k H V)).symm
        (TensorProduct.map LinearMap.id (dualEquiv k H V).symm.toLinearMap
          (coevaluation k V (trivialEquiv k H r))) := by
  rw [← mul_one (trivialEquiv k H r), ← smul_eq_mul, map_smul, map_smul, map_smul]
  rfl

/-- Coevaluation sends `r` to the sum `∑ i, r b i ⊗ b^i` over a basis and its dual basis. -/
theorem dualCoeval_apply_eq_sum (r : Trivial k H) :
    dualCoeval k H V r =
      ∑ i : Module.Basis.ofVectorSpaceIndex k V,
        tmul k H (trivialEquiv k H r • Module.Basis.ofVectorSpace k V i)
          ((dualEquiv k H V).symm ((Module.Basis.ofVectorSpace k V).coord i)) := by
  rw [dualCoeval_apply, ← mul_one (trivialEquiv k H r), ← smul_eq_mul, map_smul,
    coevaluation_apply_one]
  simp [Finset.smul_sum, TensorProduct.smul_tmul']

/-- **First zigzag identity.** Coevaluation on the right of a functional, followed by
reassociation and evaluation, returns the functional. -/
theorem lid_comp_dualEval_assoc_dualCoeval :
    (lid k H (Dual k H V)).toLinearMap ∘ₗ tensorMap k H (dualEval k H V) LinearMap.id ∘ₗ
        (assoc k H (Dual k H V) V (Dual k H V)).symm.toLinearMap ∘ₗ
          tensorMap k H LinearMap.id (dualCoeval k H V) =
      (rid k H (Dual k H V)).toLinearMap := by
  ext φ r
  apply (dualEquiv k H V).injective
  -- Transport Mathlib's triangle identity `contractLeft_assoc_coevaluation`.
  have h := congr_arg (TensorProduct.lid k _) <| LinearMap.congr_fun
    (contractLeft_assoc_coevaluation k V) (dualEquiv k H V φ ⊗ₜ trivialEquiv k H r)
  simp only [LinearMap.comp_apply, LinearMap.lTensor_tmul, LinearEquiv.coe_coe,
    TensorProduct.rid_tmul, TensorProduct.lid_symm_apply, TensorProduct.lid_tmul, one_smul] at h
  simp only [LinearMap.comp_apply, LinearEquiv.coe_coe, tensorMap_tmul, LinearMap.id_apply,
    rid_tmul, map_smul]
  rw [← h, dualCoeval_apply]
  generalize coevaluation k V (trivialEquiv k H r) = y
  induction y using TensorProduct.inductionOn with
  | add y z hy hz => simp only [map_add, tmul_add, TensorProduct.tmul_add, hy, hz]
  | tmul v ψ => simp

/-- **Second zigzag identity.** Coevaluation on the left of a vector, followed by
reassociation and evaluation, returns the vector. -/
theorem rid_comp_dualEval_assoc_dualCoeval :
    (rid k H V).toLinearMap ∘ₗ tensorMap k H LinearMap.id (dualEval k H V) ∘ₗ
        (assoc k H V (Dual k H V) V).toLinearMap ∘ₗ
          tensorMap k H (dualCoeval k H V) LinearMap.id =
      (lid k H V).toLinearMap := by
  ext r v
  -- Transport Mathlib's triangle identity `contractLeft_assoc_coevaluation'`.
  have h := congr_arg (TensorProduct.rid k _) <| LinearMap.congr_fun
    (contractLeft_assoc_coevaluation' k V) (trivialEquiv k H r ⊗ₜ v)
  simp only [LinearMap.comp_apply, LinearMap.rTensor_tmul, LinearEquiv.coe_coe,
    TensorProduct.lid_tmul, TensorProduct.rid_symm_apply, TensorProduct.rid_tmul, one_smul] at h
  simp only [LinearMap.comp_apply, LinearEquiv.coe_coe, tensorMap_tmul, LinearMap.id_apply,
    lid_tmul]
  rw [← h, dualCoeval_apply]
  generalize coevaluation k V (trivialEquiv k H r) = y
  induction y using TensorProduct.inductionOn with
  | add y z hy hz => simp only [map_add, TensorProduct.add_tmul, add_tmul, hy, hz]
  | tmul w ψ => simp

end Coevaluation

end TauCeti.BialgebraModule
