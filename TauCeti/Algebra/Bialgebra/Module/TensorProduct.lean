/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import Mathlib.RingTheory.Bialgebra.Basic
public import Mathlib.RingTheory.TensorProduct.Finite
public import TauCeti.Algebra.TensorProduct.Module

/-!
# Coproduct actions on tensor products of modules

For a bialgebra `H` over a commutative semiring `R`, its coproduct acts on the tensor product
of two `H`-modules. `BialgebraModule.Tensor` is a type synonym of the native `R`-tensor
product, with this coproduct action. A synonym is necessary because the native tensor
product's left-factor scalar action would otherwise compete with the coproduct action.
The original factor `R`-module structures are retained; `tensorEquiv` identifies the base action
with the native tensor action.

`tensorEquiv` identifies the underlying `R`-module with the native tensor product; `tmul`
constructs pure tensors. `tensorMap` tensors native `H`-linear intertwiners.

The coproduct action restricts `tensorPairAction` along `Bialgebra.comulAlgHom`.

`BialgebraModule.Trivial` is the base semiring with `H` acting through its counit. The
associativity equivalence `assoc` and the unit equivalences `lid` and `rid` are the native
tensor-product equivalences, which are `H`-linear by coassociativity and the two counit laws.
Together with the trivial module these are the data of the monoidal structure on modules over a
bialgebra; see C. Kassel, *Quantum Groups*, Chapter III.
-/

public section

open scoped TensorProduct

namespace TauCeti.BialgebraModule

/-- The tensor product over `R`, with a separate carrier for the coproduct action of `H`.

The synonym separates that action from the native tensor product's left-factor action.
The module structures reuse the native tensor structures locally;
the action itself is characterized by `tensorEquiv_smul`.
Its base action agrees with the native tensor action under `tensorEquiv`. -/
def Tensor (R _H M N : Type*) [CommSemiring R]
    [AddCommMonoid M] [Module R M] [AddCommMonoid N] [Module R N] := M ⊗[R] N

variable (R H M N : Type*) [CommSemiring R]
variable [AddCommMonoid M] [Module R M] [AddCommMonoid N] [Module R N]

instance : AddCommMonoid (Tensor R H M N) := inferInstanceAs (AddCommMonoid (M ⊗[R] N))

instance (R H M N : Type*) [CommSemiring R] [AddCommGroup M] [Module R M]
    [AddCommGroup N] [Module R N] : AddCommGroup (Tensor R H M N) :=
  inferInstanceAs (AddCommGroup (M ⊗[R] N))

section Action

variable [Semiring H] [Bialgebra R H]
variable [Module H M] [IsScalarTower R H M] [Module H N] [IsScalarTower R H N]

/-- The representation of `H` on the native tensor product obtained from its coproduct. -/
noncomputable def tensorAction : H →ₐ[R] Module.End R (M ⊗[R] N) :=
  (tensorPairAction R H M N).comp (Bialgebra.comulAlgHom R H)

/-- The coproduct action is the pair action applied to the coproduct. -/
theorem tensorAction_apply (h : H) (x : M ⊗[R] N) :
    tensorAction R H M N h x =
      tensorPairAction R H M N (Coalgebra.comul h) x := (rfl)

/-- The coproduct module structure on the tensor carrier. -/
@[no_expose] noncomputable instance : Module H (Tensor R H M N) :=
  Module.compHom (M ⊗[R] N) (tensorAction R H M N).toRingHom

/-- The base action is restriction of the coproduct action along the algebra map.

For the canonical algebra structure when `H = R`, this presentation also aligns the two
scalar actions.
The underlying equivalence below identifies it with the original native tensor action.
The priority keeps this presentation ahead of generic natural and integer scalar actions. -/
noncomputable instance (priority := 1100) : Module R (Tensor R H M N) :=
  Module.compHom (Tensor R H M N) (algebraMap R H)

/-- The coproduct module is compatible with the caller's base scalar action. -/
instance : IsScalarTower R H (Tensor R H M N) := IsScalarTower.of_compHom R H (Tensor R H M N)

/-- The underlying `R`-linear identification with the native tensor product. -/
noncomputable def tensorEquiv : Tensor R H M N ≃ₗ[R] M ⊗[R] N :=
  let e : Tensor R H M N ≃+ M ⊗[R] N := AddEquiv.refl _
  e.toLinearEquiv fun r x => LinearMap.congr_fun ((tensorAction R H M N).commutes r) x

/-- Finite base modules have a finite tensor product with the coproduct action. -/
instance [Module.Finite R M] [Module.Finite R N] : Module.Finite R (Tensor R H M N) :=
  Module.Finite.of_surjective (tensorEquiv R H M N).symm.toLinearMap
    (tensorEquiv R H M N).symm.surjective

variable {M N} in
/-- A pure tensor in the carrier with the coproduct action. -/
noncomputable def tmul (m : M) (n : N) : Tensor R H M N :=
  (tensorEquiv R H M N).symm (m ⊗ₜ[R] n)

/-- The underlying equivalence sends a pure tensor to the native pure tensor. -/
@[simp] theorem tensorEquiv_tmul (m : M) (n : N) :
    tensorEquiv R H M N (tmul R H m n) = m ⊗ₜ[R] n := by
  simp [tmul]

/-- The inverse underlying equivalence constructs pure tensors. -/
@[simp] theorem tensorEquiv_symm_tmul (m : M) (n : N) :
    (tensorEquiv R H M N).symm (m ⊗ₜ[R] n) = tmul R H m n := (rfl)

variable {M N} in
/-- Pure tensors are additive in the first factor. -/
@[simp] theorem add_tmul (m m' : M) (n : N) :
    tmul R H (m + m') n = tmul R H m n + tmul R H m' n := by
  apply (tensorEquiv R H M N).injective
  simp [TensorProduct.add_tmul]

variable {M N} in
/-- Pure tensors are additive in the second factor. -/
@[simp] theorem tmul_add (m : M) (n n' : N) :
    tmul R H m (n + n') = tmul R H m n + tmul R H m n' := by
  apply (tensorEquiv R H M N).injective
  simp [TensorProduct.tmul_add]

variable {M N} in
/-- A zero first factor gives the zero tensor. -/
@[simp] theorem zero_tmul (n : N) : tmul R H (0 : M) n = 0 := by
  apply (tensorEquiv R H M N).injective
  simp

variable {M N} in
/-- A zero second factor gives the zero tensor. -/
@[simp] theorem tmul_zero (m : M) : tmul R H m (0 : N) = 0 := by
  apply (tensorEquiv R H M N).injective
  simp

variable {M N} in
/-- Base scalars may be applied to the first factor. -/
theorem smul_tmul' (r : R) (m : M) (n : N) :
    r • tmul R H m n = tmul R H (r • m) n := by
  apply (tensorEquiv R H M N).injective
  simp [TensorProduct.smul_tmul']

variable {M N} in
/-- Base scalars may be applied to the second factor. -/
@[simp] theorem tmul_smul (r : R) (m : M) (n : N) :
    tmul R H m (r • n) = r • tmul R H m n := by
  apply (tensorEquiv R H M N).injective
  simp

/-- Negating the first factor negates the pure tensor. -/
@[simp] theorem neg_tmul {M N : Type*} [AddCommGroup M] [Module R M] [Module H M]
    [IsScalarTower R H M] [AddCommGroup N] [Module R N] [Module H N] [IsScalarTower R H N]
    (m : M) (n : N) : tmul R H (-m) n = -tmul R H m n := by
  apply (tensorEquiv R H M N).injective
  simp [TensorProduct.neg_tmul]

/-- Negating the second factor negates the pure tensor. -/
@[simp] theorem tmul_neg {M N : Type*} [AddCommGroup M] [Module R M] [Module H M]
    [IsScalarTower R H M] [AddCommGroup N] [Module R N] [Module H N] [IsScalarTower R H N]
    (m : M) (n : N) : tmul R H m (-n) = -tmul R H m n := by
  apply (tensorEquiv R H M N).injective
  simp [TensorProduct.tmul_neg]

variable {R H M N} in
/-- Prove a proposition about coproduct tensors by pure tensors and addition. -/
@[elab_as_elim] theorem Tensor.inductionOn {P : Tensor R H M N → Prop}
    (x : Tensor R H M N) (htmul : ∀ m n, P (tmul R H m n))
    (hadd : ∀ x y, P x → P y → P (x + y)) : P x := by
  have h : ∀ y : M ⊗[R] N, P ((tensorEquiv R H M N).symm y) := by
    intro y
    induction y using TensorProduct.inductionOn with
    | tmul m n => exact htmul m n
    | add y z hy hz => simpa only [map_add] using hadd _ _ hy hz
  simpa using h (tensorEquiv R H M N x)

variable {R H M N} in
/-- Two `H`-linear maps from the coproduct tensor carrier agree if they agree on pure tensors. -/
@[ext] theorem Tensor.ext {P : Type*} [AddCommMonoid P] [Module H P]
    {f g : Tensor R H M N →ₗ[H] P}
    (h : ∀ m n, f (tmul R H m n) = g (tmul R H m n)) : f = g := by
  apply LinearMap.ext
  intro x
  exact Tensor.inductionOn x h fun x y hx hy ↦ by simp only [map_add, hx, hy]

/-- The underlying equivalence expresses the action through the coproduct representation. -/
@[simp]
theorem tensorEquiv_smul (h : H) (x : Tensor R H M N) :
    tensorEquiv R H M N (h • x) =
      tensorAction R H M N h (tensorEquiv R H M N x) := (rfl)

variable {M' N' : Type*}
variable [AddCommMonoid M'] [Module R M'] [Module H M'] [IsScalarTower R H M']
variable [AddCommMonoid N'] [Module R N'] [Module H N'] [IsScalarTower R H N']

variable {M N} in
/-- The tensor product of native `H`-linear intertwiners, for the coproduct actions. -/
noncomputable def tensorMap (f : M →ₗ[H] M') (g : N →ₗ[H] N') :
    Tensor R H M N →ₗ[H] Tensor R H M' N' where
  toAddHom := ((tensorEquiv R H M' N').symm.toLinearMap.comp
    ((TensorProduct.map (f.restrictScalars R) (g.restrictScalars R)).comp
      (tensorEquiv R H M N).toLinearMap)).toAddHom
  map_smul' h x := by
    apply (tensorEquiv R H M' N').injective
    simpa [tensorAction_apply] using
      tensorPairAction_natural R H f g (Coalgebra.comul h) (tensorEquiv R H M N x)

variable {M N} in
/-- The underlying map of a tensor intertwiner is the native tensor product of maps. -/
@[simp] theorem tensorEquiv_tensorMap (f : M →ₗ[H] M') (g : N →ₗ[H] N')
    (x : Tensor R H M N) :
    tensorEquiv R H M' N' (tensorMap R H f g x) =
      TensorProduct.map (f.restrictScalars R) (g.restrictScalars R)
        (tensorEquiv R H M N x) := (rfl)

variable {M N} in
/-- A tensor intertwiner acts on pure tensors by its two component maps. -/
@[simp] theorem tensorMap_tmul (f : M →ₗ[H] M') (g : N →ₗ[H] N') (m : M) (n : N) :
    tensorMap R H f g (tmul R H m n) = tmul R H (f m) (g n) := by
  apply (tensorEquiv R H M' N').injective
  simp

/-- Tensoring the identity intertwiners gives the identity. -/
@[simp] theorem tensorMap_id :
    tensorMap R H (LinearMap.id : M →ₗ[H] M) (LinearMap.id : N →ₗ[H] N) =
      LinearMap.id := by
  apply Tensor.ext
  intro m n
  simp

variable {M'' N'' : Type*}
variable [AddCommMonoid M''] [Module R M''] [Module H M''] [IsScalarTower R H M'']
variable [AddCommMonoid N''] [Module R N''] [Module H N''] [IsScalarTower R H N'']

variable {M N} in
/-- Tensor products of intertwiners preserve composition. -/
@[simp] theorem tensorMap_comp (f : M →ₗ[H] M') (f' : M' →ₗ[H] M'')
    (g : N →ₗ[H] N') (g' : N' →ₗ[H] N'') :
    tensorMap R H (f'.comp f) (g'.comp g) =
      (tensorMap R H f' g').comp (tensorMap R H f g) := by
  apply Tensor.ext
  intro m n
  simp

end Action

section Coherence

variable [Semiring H] [Bialgebra R H]
variable [Module H M] [IsScalarTower R H M] [Module H N] [IsScalarTower R H N]
variable (P : Type*) [AddCommMonoid P] [Module R P] [Module H P] [IsScalarTower R H P]

variable {M N P} in
/-- The left-nested coproduct action on a pure triple tensor, reassociated, is the action of
the reassociated iterated coproduct. -/
private theorem assoc_tensorPairAction_left (m : M) (n : N) (p : P) (t : H ⊗[R] H) :
    TensorProduct.assoc R M N P
        (TensorProduct.congr (tensorEquiv R H M N) (LinearEquiv.refl R P)
          (tensorPairAction R H (Tensor R H M N) P t (tmul R H m n ⊗ₜ[R] p))) =
      TensorProduct.map ((LinearMap.toSpanSingleton H M m).restrictScalars R)
        (TensorProduct.map ((LinearMap.toSpanSingleton H N n).restrictScalars R)
          ((LinearMap.toSpanSingleton H P p).restrictScalars R))
        (TensorProduct.assoc R H H H (Coalgebra.comul.rTensor H t)) := by
  induction t using TensorProduct.inductionOn with
  | add t u ht hu => simp only [map_add, LinearMap.add_apply, ht, hu]
  | tmul a b =>
    simp only [tensorPairAction_tmul, TensorProduct.congr_tmul, LinearMap.rTensor_tmul,
      LinearEquiv.refl_apply, tensorEquiv_smul, tensorEquiv_tmul, tensorAction_apply]
    induction Coalgebra.comul (R := R) a using TensorProduct.inductionOn with
    | add s s' hs hs' => simp only [map_add, LinearMap.add_apply, TensorProduct.add_tmul, hs, hs']
    | tmul c d => simp

variable {M N P} in
/-- The right-nested coproduct action on a pure triple tensor is the action of the iterated
coproduct. -/
private theorem tensorPairAction_right (m : M) (n : N) (p : P) (t : H ⊗[R] H) :
    TensorProduct.congr (LinearEquiv.refl R M) (tensorEquiv R H N P)
        (tensorPairAction R H M (Tensor R H N P) t (m ⊗ₜ[R] tmul R H n p)) =
      TensorProduct.map ((LinearMap.toSpanSingleton H M m).restrictScalars R)
        (TensorProduct.map ((LinearMap.toSpanSingleton H N n).restrictScalars R)
          ((LinearMap.toSpanSingleton H P p).restrictScalars R))
        (Coalgebra.comul.lTensor H t) := by
  induction t using TensorProduct.inductionOn with
  | add t u ht hu => simp only [map_add, LinearMap.add_apply, ht, hu]
  | tmul a b =>
    simp only [tensorPairAction_tmul, TensorProduct.congr_tmul, LinearMap.lTensor_tmul,
      LinearEquiv.refl_apply, tensorEquiv_smul, tensorEquiv_tmul, tensorAction_apply]
    induction Coalgebra.comul (R := R) b using TensorProduct.inductionOn with
    | add s s' hs hs' =>
      simp only [map_add, LinearMap.add_apply, TensorProduct.tmul_add, hs, hs']
    | tmul c d => simp

/-- The underlying `R`-linear associativity equivalence of coproduct tensor products. -/
private noncomputable def assocAux :
    Tensor R H (Tensor R H M N) P ≃ₗ[R] Tensor R H M (Tensor R H N P) :=
  (tensorEquiv R H (Tensor R H M N) P).trans <|
    (TensorProduct.congr (tensorEquiv R H M N) (LinearEquiv.refl R P)).trans <|
      (TensorProduct.assoc R M N P).trans <|
        (TensorProduct.congr (LinearEquiv.refl R M) (tensorEquiv R H N P)).symm.trans
          (tensorEquiv R H M (Tensor R H N P)).symm

private theorem assocAux_tmul (m : M) (n : N) (p : P) :
    assocAux R H M N P (tmul R H (tmul R H m n) p) = tmul R H m (tmul R H n p) := by
  simp [assocAux]

private theorem assocAux_smul (h : H) (x : Tensor R H (Tensor R H M N) P) :
    assocAux R H M N P (h • x) = h • assocAux R H M N P x := by
  induction x using Tensor.inductionOn with
  | hadd x y hx hy => simp only [smul_add, map_add, hx, hy]
  | htmul y p =>
    induction y using Tensor.inductionOn with
    | hadd y z hy hz => simp only [add_tmul, smul_add, map_add, hy, hz]
    | htmul m n =>
      rw [assocAux_tmul]
      apply (tensorEquiv R H M (Tensor R H N P)).injective
      apply (TensorProduct.congr (LinearEquiv.refl R M) (tensorEquiv R H N P)).injective
      have hl := assoc_tensorPairAction_left (R := R) (H := H) m n p (Coalgebra.comul h)
      have hr := tensorPairAction_right (R := R) (H := H) m n p (Coalgebra.comul h)
      simp only [Coalgebra.coassoc_apply] at hl
      simp only [assocAux, LinearEquiv.trans_apply, tensorEquiv_smul, tensorAction_apply,
        tensorEquiv_tmul, LinearEquiv.apply_symm_apply]
      rw [← hr] at hl
      exact hl

/-- The associativity equivalence of coproduct tensor products. It is `H`-linear because the
coproduct is coassociative. -/
noncomputable def assoc :
    Tensor R H (Tensor R H M N) P ≃ₗ[H] Tensor R H M (Tensor R H N P) where
  __ := assocAux R H M N P
  map_smul' := assocAux_smul R H M N P

/-- Underneath, the associativity equivalence is the associativity equivalence of native
tensor products. -/
theorem tensorEquiv_assoc (x : Tensor R H (Tensor R H M N) P) :
    tensorEquiv R H M (Tensor R H N P) (assoc R H M N P x) =
      TensorProduct.map LinearMap.id (tensorEquiv R H N P).symm.toLinearMap
        (TensorProduct.assoc R M N P
          (TensorProduct.map (tensorEquiv R H M N).toLinearMap LinearMap.id
            (tensorEquiv R H (Tensor R H M N) P x))) := by
  simp [assoc, assocAux, TensorProduct.congr]

variable {M N P} in
/-- The associativity equivalence reassociates pure tensors. -/
@[simp] theorem assoc_tmul (m : M) (n : N) (p : P) :
    assoc R H M N P (tmul R H (tmul R H m n) p) = tmul R H m (tmul R H n p) :=
  assocAux_tmul R H M N P m n p

variable {M N P} in
/-- The inverse associativity equivalence reassociates pure tensors. -/
@[simp] theorem assoc_symm_tmul (m : M) (n : N) (p : P) :
    (assoc R H M N P).symm (tmul R H m (tmul R H n p)) = tmul R H (tmul R H m n) p := by
  rw [LinearEquiv.symm_apply_eq, assoc_tmul]

end Coherence

section Trivial

/-- The base semiring `R`, with a separate carrier for the action of `H` through its counit.

This trivial module is the unit for the coproduct tensor product. As for `Tensor`, the base
action is restriction of the `H`-action along the algebra map, and `trivialEquiv` identifies
it with the native action of `R` on itself. -/
def Trivial (R _H : Type*) := R

noncomputable instance : AddCommMonoid (Trivial R H) := inferInstanceAs (AddCommMonoid R)

noncomputable instance (R H : Type*) [CommRing R] : AddCommGroup (Trivial R H) :=
  inferInstanceAs (AddCommGroup R)

variable [Semiring H] [Bialgebra R H]

/-- The action of `H` on the trivial module, through the counit. -/
@[no_expose] noncomputable instance : Module H (Trivial R H) :=
  (Module.compHom R (Bialgebra.counitAlgHom R H).toRingHom : Module H R)

/-- The base action on the trivial module is restriction of the counit action along the
algebra map. -/
noncomputable instance (priority := 1100) : Module R (Trivial R H) :=
  Module.compHom (Trivial R H) (algebraMap R H)

/-- The counit module is compatible with its base scalar action. -/
instance : IsScalarTower R H (Trivial R H) := IsScalarTower.of_compHom R H (Trivial R H)

/-- The underlying `R`-linear identification of the trivial module with `R`. -/
noncomputable def trivialEquiv : Trivial R H ≃ₗ[R] R :=
  let e : Trivial R H ≃+ R := AddEquiv.refl _
  e.toLinearEquiv fun r x => by
    -- The base action on `Trivial R H` is defined by `Module.compHom` twice, so `r • x`
    -- unfolds to multiplication by the counit of `algebraMap R H r`; no lemma states this.
    change Coalgebra.counit (R := R) (algebraMap R H r) * e x = r • e x
    rw [Bialgebra.counit_algebraMap, smul_eq_mul]

/-- An element of `H` acts on the trivial module by multiplication by its counit. -/
@[simp]
theorem trivialEquiv_smul (h : H) (x : Trivial R H) :
    trivialEquiv R H (h • x) = Coalgebra.counit (R := R) h * trivialEquiv R H x := (rfl)

/-- The trivial module is finite over the base. -/
instance : Module.Finite R (Trivial R H) :=
  Module.Finite.of_surjective (trivialEquiv R H).symm.toLinearMap
    (trivialEquiv R H).symm.surjective

variable [Module H M] [IsScalarTower R H M]

variable {M} in
/-- On a pure tensor with a trivial factor, the coproduct action is the counit contraction
followed by the action on the other factor. -/
private theorem lid_tensorPairAction (r : Trivial R H) (m : M) (t : H ⊗[R] H) :
    TensorProduct.lid R M
        (TensorProduct.congr (trivialEquiv R H) (LinearEquiv.refl R M)
          (tensorPairAction R H (Trivial R H) M t (r ⊗ₜ[R] m))) =
      trivialEquiv R H r •
        TensorProduct.lid R H (Coalgebra.counit.rTensor H t) • m := by
  induction t using TensorProduct.inductionOn with
  | add t u ht hu => simp only [map_add, LinearMap.add_apply, ht, hu, add_smul, smul_add]
  | tmul a b => simp [mul_smul, smul_comm (Coalgebra.counit (R := R) a)]

variable {M} in
/-- On a pure tensor with a trivial factor on the right, the coproduct action is the counit
contraction followed by the action on the other factor. -/
private theorem rid_tensorPairAction (m : M) (r : Trivial R H) (t : H ⊗[R] H) :
    TensorProduct.rid R M
        (TensorProduct.congr (LinearEquiv.refl R M) (trivialEquiv R H)
          (tensorPairAction R H M (Trivial R H) t (m ⊗ₜ[R] r))) =
      trivialEquiv R H r •
        TensorProduct.rid R H (Coalgebra.counit.lTensor H t) • m := by
  induction t using TensorProduct.inductionOn with
  | add t u ht hu => simp only [map_add, LinearMap.add_apply, ht, hu, add_smul, smul_add]
  | tmul a b => simp [mul_smul, smul_comm (Coalgebra.counit (R := R) b)]

/-- The underlying `R`-linear left unit equivalence of the coproduct tensor product. -/
private noncomputable def lidAux : Tensor R H (Trivial R H) M ≃ₗ[R] M :=
  (tensorEquiv R H (Trivial R H) M).trans <|
    (TensorProduct.congr (trivialEquiv R H) (LinearEquiv.refl R M)).trans (TensorProduct.lid R M)

private theorem lidAux_smul (h : H) (x : Tensor R H (Trivial R H) M) :
    lidAux R H M (h • x) = h • lidAux R H M x := by
  induction x using Tensor.inductionOn with
  | hadd x y hx hy => simp only [smul_add, map_add, hx, hy]
  | htmul r m =>
    have := lid_tensorPairAction R H r m (Coalgebra.comul h)
    simp only [Coalgebra.rTensor_counit_comul, TensorProduct.lid_tmul, one_smul] at this
    simpa [lidAux, tensorAction_apply, smul_comm h] using this

/-- The left unit equivalence of the coproduct tensor product. It is `H`-linear by the
left counit law. -/
noncomputable def lid : Tensor R H (Trivial R H) M ≃ₗ[H] M where
  __ := lidAux R H M
  map_smul' := lidAux_smul R H M

/-- Underneath, the left unit equivalence is the native left unit equivalence. -/
theorem lid_apply (x : Tensor R H (Trivial R H) M) :
    lid R H M x =
      TensorProduct.lid R M (TensorProduct.map (trivialEquiv R H).toLinearMap LinearMap.id
        (tensorEquiv R H (Trivial R H) M x)) := by
  simp [lid, lidAux, TensorProduct.congr]

variable {M} in
/-- The left unit equivalence scales by the trivial factor. -/
@[simp] theorem lid_tmul (r : Trivial R H) (m : M) :
    lid R H M (tmul R H r m) = trivialEquiv R H r • m := by
  simp [lid, lidAux]

variable {M} in
/-- The inverse left unit equivalence inserts the unit of the trivial module. -/
@[simp] theorem lid_symm_apply (m : M) :
    (lid R H M).symm m = tmul R H ((trivialEquiv R H).symm 1) m := by
  rw [LinearEquiv.symm_apply_eq, lid_tmul, LinearEquiv.apply_symm_apply, one_smul]

/-- The underlying `R`-linear right unit equivalence of the coproduct tensor product. -/
private noncomputable def ridAux : Tensor R H M (Trivial R H) ≃ₗ[R] M :=
  (tensorEquiv R H M (Trivial R H)).trans <|
    (TensorProduct.congr (LinearEquiv.refl R M) (trivialEquiv R H)).trans (TensorProduct.rid R M)

private theorem ridAux_smul (h : H) (x : Tensor R H M (Trivial R H)) :
    ridAux R H M (h • x) = h • ridAux R H M x := by
  induction x using Tensor.inductionOn with
  | hadd x y hx hy => simp only [smul_add, map_add, hx, hy]
  | htmul m r =>
    have := rid_tensorPairAction R H m r (Coalgebra.comul h)
    simp only [Coalgebra.lTensor_counit_comul, TensorProduct.rid_tmul, one_smul] at this
    simpa [ridAux, tensorAction_apply, smul_comm h] using this

/-- The right unit equivalence of the coproduct tensor product. It is `H`-linear by the
right counit law. -/
noncomputable def rid : Tensor R H M (Trivial R H) ≃ₗ[H] M where
  __ := ridAux R H M
  map_smul' := ridAux_smul R H M

/-- Underneath, the right unit equivalence is the native right unit equivalence. -/
theorem rid_apply (x : Tensor R H M (Trivial R H)) :
    rid R H M x =
      TensorProduct.rid R M (TensorProduct.map LinearMap.id (trivialEquiv R H).toLinearMap
        (tensorEquiv R H M (Trivial R H) x)) := by
  simp [rid, ridAux, TensorProduct.congr]

variable {M} in
/-- The right unit equivalence scales by the trivial factor. -/
@[simp] theorem rid_tmul (m : M) (r : Trivial R H) :
    rid R H M (tmul R H m r) = trivialEquiv R H r • m := by
  simp [rid, ridAux]

variable {M} in
/-- The inverse right unit equivalence inserts the unit of the trivial module. -/
@[simp] theorem rid_symm_apply (m : M) :
    (rid R H M).symm m = tmul R H m ((trivialEquiv R H).symm 1) := by
  rw [LinearEquiv.symm_apply_eq, rid_tmul, LinearEquiv.apply_symm_apply, one_smul]

end Trivial

end TauCeti.BialgebraModule
