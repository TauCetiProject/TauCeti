/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import Mathlib.LinearAlgebra.Dual.Defs
public import Mathlib.LinearAlgebra.RootSystem.Hom
import TauCeti.LinearAlgebra.RootSystem.Basic
import TauCeti.LinearAlgebra.RootSystem.HomInvariance
import TauCeti.LinearAlgebra.RootSystem.Map

/-!
# Composing, inverting and conjugating equivalences of root pairings

Equivalences of root pairings form a groupoid: `RootPairing.Equiv.comp` composes them,
`RootPairing.Equiv.id` is the identity and `RootPairing.Equiv.symm` inverts. This file records the
laws of that groupoid which relate composition and inversion, together with the weight- and
coweight-space linear equivalences of a composite.

Conjugation by an equivalence `e : P.Equiv Q` is then built out of those laws: it carries an
automorphism `g` of `P` to `e ∘ g ∘ e⁻¹`, an automorphism of `Q`, and does so compatibly with the
group structures, with the weight-space, coweight-space and index-set data of an automorphism, and
with the actions of the automorphism groups on weight vectors and on root indices.

The statements are about two or three root pairings with unrelated index sets, weight spaces and
coweight spaces; nothing here needs any finiteness, reducedness or crystallographic hypothesis.
Laws about a single pairing are already available from the `Group (RootPairing.Equiv P P)`
instance, so they are not restated here; only their translation into the weight maps and index
permutations of products and powers of automorphisms is recorded.

## Main definitions

* `RootPairing.Equiv.autCongr`: conjugation by an equivalence, as a group isomorphism
  `P.Aut ≃* Q.Aut`.
* `RootPairing.mapDual` and `RootPairing.equivMapDual`: pushforward of `P` along `e : ι ≃ ι₂` and
  `f : M ≃ₗ[R] M₂` onto `M₂` paired with `Module.Dual R M₂` by evaluation, and the canonical
  equivalence `P.Equiv (P.mapDual e f)`.

## Main results

* `RootPairing.Equiv.self_comp_symm` and `RootPairing.Equiv.symm_comp_self`: an equivalence
  composes with its inverse to the identity, in both orders.
* `RootPairing.Equiv.symm_comp`: the inverse of a composite is the composite of the inverses in
  the reverse order.
* `RootPairing.Equiv.weightEquiv_comp` and `RootPairing.Equiv.coweightEquiv_comp`: the weight- and
  coweight-space equivalences of a composite.
* `RootPairing.Equiv.weightEquiv_autCongr_apply`,
  `RootPairing.Equiv.coweightEquiv_autCongr_apply` and
  `RootPairing.Equiv.indexEquiv_autCongr_apply`: the weight-space map, the coweight-space map and
  the index permutation of a conjugated automorphism are the conjugates of the originals.
* `RootPairing.Equiv.smul_index_eq_indexEquiv`: an automorphism acts on root indices through its
  index permutation.
* `RootPairing.Equiv.indexEquiv_mul_apply`, `RootPairing.Equiv.weightMap_mul_apply`, and
  `RootPairing.Equiv.reflection_weightMap_apply`: index-permutation and weight-map evaluation on
  products and reflections of automorphisms.
* `RootPairing.Equiv.indexEquiv_reflection_comm_of_indexEquiv_eq`,
  `RootPairing.Equiv.pairing_indexEquiv_comm_of_apply_apply`,
  `RootPairing.Equiv.indexEquiv_reflection_mul_comm_of_pairing_eq_zero`, and
  `RootPairing.Equiv.indexEquiv_reflection_braid_comm_of_pairing_eq_neg_one`: fixed-root and
  period-two orbit reflection commutators with an automorphism `σ`.
* `RootPairing.Equiv.autCongr_smul`, `RootPairing.Equiv.autCongr_smul_index`,
  `RootPairing.Equiv.indexEquiv_apply_of_autCongr_eq`, and
  `RootPairing.Equiv.autCongr_eq_iff_weightEquiv_comp_weightMap`: conjugation transports the actions
  on weight vectors and on root indices, and characterizes intertwining along `weightEquiv`.
* `RootPairing.Equiv.autCongr_id` and `RootPairing.Equiv.autCongr_comp`: conjugation is
  functorial.
* `RootPairing.Equiv.indexEquiv_pow` and `RootPairing.Equiv.weightMap_pow`: the index
  permutation and the weight map of a power of an automorphism are the powers of those of the
  automorphism.
* `RootPairing.Hom.weightMap_comp_of_indexEquiv`,
  `RootPairing.Hom.indexEquiv_apply_of_weightMap_comp`,
  `RootPairing.Equiv.weightEquiv_comp_weightMap_of_indexEquiv`, and
  `RootPairing.Equiv.indexEquiv_apply_of_weightEquiv_comp_weightMap`: intertwining of weight-space
  endomorphisms and root-index permutations.

## References

* N. Bourbaki, *Lie Groups and Lie Algebras, Chapters 4--6*, Ch. VI, §1.
-/

public section

namespace RootPairing.Equiv

variable {ι ι₂ ι₃ R M N M₂ N₂ M₃ N₃ : Type*} [CommRing R]
  [AddCommGroup M] [Module R M] [AddCommGroup N] [Module R N]
  [AddCommGroup M₂] [Module R M₂] [AddCommGroup N₂] [Module R N₂]
  [AddCommGroup M₃] [Module R M₃] [AddCommGroup N₃] [Module R N₃]
  {P : RootPairing ι R M N} {Q : RootPairing ι₂ R M₂ N₂} {S : RootPairing ι₃ R M₃ N₃}

/-- An equivalence of root pairings composed with its inverse is the identity of the target. -/
@[simp]
theorem self_comp_symm (e : P.Equiv Q) :
    RootPairing.Equiv.comp e (RootPairing.Equiv.symm P Q e) = RootPairing.Equiv.id Q := by
  ext x <;> simp

/-- The inverse of an equivalence of root pairings composed with it is the identity of the
source. -/
@[simp]
theorem symm_comp_self (e : P.Equiv Q) :
    RootPairing.Equiv.comp (RootPairing.Equiv.symm P Q e) e = RootPairing.Equiv.id P := by
  ext x <;> simp

/-- The weight-space equivalence of a composite is the composite of the weight-space
equivalences. -/
@[simp]
theorem weightEquiv_comp (e : P.Equiv Q) (f : Q.Equiv S) :
    weightEquiv (RootPairing.Equiv.comp f e) = e.weightEquiv ≪≫ₗ f.weightEquiv :=
  LinearEquiv.ext fun _ ↦ rfl

/-- The coweight-space equivalence of a composite is the composite of the coweight-space
equivalences, in the reverse order. -/
@[simp]
theorem coweightEquiv_comp (e : P.Equiv Q) (f : Q.Equiv S) :
    RootPairing.Equiv.coweightEquiv (RootPairing.Equiv.comp f e) =
      f.coweightEquiv ≪≫ₗ e.coweightEquiv :=
  LinearEquiv.ext fun _ ↦ rfl

/-- The inverse of a composite of equivalences is the composite of the inverses, in the reverse
order. -/
@[simp]
theorem symm_comp (e : P.Equiv Q) (f : Q.Equiv S) :
    RootPairing.Equiv.symm P S (RootPairing.Equiv.comp f e) =
      RootPairing.Equiv.comp (RootPairing.Equiv.symm P Q e) (RootPairing.Equiv.symm Q S f) := by
  ext x <;> simp

/-- The action of the automorphism group on root indices is through `indexEquiv`.

Not a `simp` lemma: it would rewrite the left-hand side of the `simp` lemma
`RootPairing.Equiv.autCongr_smul_index`, which is stated for the action. -/
theorem smul_index_eq_indexEquiv (g : Aut P) (i : ι) :
    g • i = g.indexEquiv i :=
  (rfl)

/-- The index permutation of a product of automorphisms is the composition of their index
permutations. -/
theorem indexEquiv_mul_apply (f g : Aut P) (i : ι) :
    (f * g).indexEquiv i = f.indexEquiv (g.indexEquiv i) :=
  (rfl)

/-- The weight-space map of `RootPairing.Equiv.reflection P i` is `P.reflection i`. -/
theorem reflection_weightMap_apply (P : RootPairing ι R M N) (i : ι) (x : M) :
    (reflection P i).weightMap x = P.reflection i x :=
  (rfl)

/-- On root indices, reflection in a `σ`-fixed root `j` commutes with `σ`. -/
theorem indexEquiv_reflection_comm_of_indexEquiv_eq (σ : Aut P) {j : ι}
    (hfix : σ.indexEquiv j = j) (r : ι) :
    (reflection P j).indexEquiv (σ.indexEquiv r) =
      σ.indexEquiv ((reflection P j).indexEquiv r) := by
  rw [reflection_indexEquiv, σ.toHom.indexEquiv_reflectionPerm, hfix]

/-- For a local period-two root `j` (`σ² j = j`), the pairings between `j` and `σ j` are equal. -/
theorem pairing_indexEquiv_comm_of_apply_apply (σ : Aut P) {j : ι}
    (hinv : σ.indexEquiv (σ.indexEquiv j) = j) :
    P.pairing j (σ.indexEquiv j) = P.pairing (σ.indexEquiv j) j := by
  have hp := σ.toHom.pairing (i := j) (j := σ.indexEquiv j)
  rw [hinv] at hp
  exact hp.symm

/-- On root indices, the product `s_j * s_{σ j}` commutes with `σ` when `σ² j = j` and
`P.pairing (σ.indexEquiv j) j = 0`. -/
theorem indexEquiv_reflection_mul_comm_of_pairing_eq_zero (σ : Aut P) {j : ι}
    (hinv : σ.indexEquiv (σ.indexEquiv j) = j) (h0 : P.pairing (σ.indexEquiv j) j = 0) (r : ι) :
    (reflection P j * reflection P (σ.indexEquiv j)).indexEquiv (σ.indexEquiv r) =
      σ.indexEquiv ((reflection P j * reflection P (σ.indexEquiv j)).indexEquiv r) := by
  have h0' : P.pairing j (σ.indexEquiv j) = 0 :=
    (σ.pairing_indexEquiv_comm_of_apply_apply hinv).trans h0
  simp only [indexEquiv_mul_apply, reflection_indexEquiv, σ.toHom.indexEquiv_reflectionPerm, hinv]
  exact P.reflectionPerm_comm_of_isOrthogonal ⟨h0', h0⟩ (σ.indexEquiv r)

/-- On root indices, the braid product `s_j * s_{σ j} * s_j` commutes with `σ` when `σ² j = j` and
`P.pairing (σ.indexEquiv j) j = -1`. -/
theorem indexEquiv_reflection_braid_comm_of_pairing_eq_neg_one (σ : Aut P) {j : ι}
    (hinv : σ.indexEquiv (σ.indexEquiv j) = j) (hneg : P.pairing (σ.indexEquiv j) j = -1)
    (r : ι) :
    (reflection P j * reflection P (σ.indexEquiv j) * reflection P j).indexEquiv (σ.indexEquiv r) =
      σ.indexEquiv ((reflection P j * reflection P (σ.indexEquiv j) *
        reflection P j).indexEquiv r) := by
  have hneg' : P.pairing j (σ.indexEquiv j) = -1 :=
    (σ.pairing_indexEquiv_comm_of_apply_apply hinv).trans hneg
  simp only [indexEquiv_mul_apply, reflection_indexEquiv, σ.toHom.indexEquiv_reflectionPerm, hinv]
  exact P.reflectionPerm_braid_of_pairing_eq_neg_one hneg' hneg (σ.indexEquiv r)

noncomputable section Conjugation

/-- **Conjugation by an equivalence of root pairings**, as a group isomorphism of automorphism
groups: an automorphism `g` of `P` is carried to `e ∘ g ∘ e⁻¹`. -/
def autCongr (e : P.Equiv Q) : Aut P ≃* Aut Q where
  toFun g := .comp e (.comp g (.symm P Q e))
  invFun h := .comp (.symm P Q e) (.comp h e)
  left_inv g := by ext x <;> simp
  right_inv h := by ext x <;> simp
  map_mul' g₁ g₂ := by ext x <;> simp

theorem autCongr_apply (e : P.Equiv Q) (g : Aut P) :
    e.autCongr g = .comp e (.comp g (.symm P Q e)) :=
  (rfl)

theorem autCongr_symm_apply (e : P.Equiv Q) (h : Aut Q) :
    e.autCongr.symm h = .comp (.symm P Q e) (.comp h e) :=
  (rfl)

/-- The weight-space map of a conjugated automorphism is the conjugated weight-space map.

Not a `simp` lemma: `RootPairing.Equiv.weightEquiv_apply` rewrites the left-hand side to the
underlying `weightMap`, so the statement is not in `simp`-normal form. The intended interface is
`RootPairing.Equiv.autCongr_smul`, which is stated for the weight-space action. -/
theorem weightEquiv_autCongr_apply (e : P.Equiv Q) (g : Aut P) (x : M₂) :
    weightEquiv (e.autCongr g) x = e.weightEquiv (g.weightEquiv (e.weightEquiv.symm x)) :=
  (rfl)

/-- The coweight-space map of a conjugated automorphism is the conjugated coweight-space map. Note
that `RootPairing.Equiv.coweightEquiv` is contravariant, so the conjugation runs the other way
round than for weight spaces; applying `e.coweightEquiv` to both sides turns this into
`e.coweightEquiv ((e.autCongr g).coweightEquiv y) = g.coweightEquiv (e.coweightEquiv y)`.

Not a `simp` lemma, for the same reason as
`RootPairing.Equiv.weightEquiv_autCongr_apply`: `RootPairing.Equiv.coweightEquiv_apply` rewrites
the left-hand side to the underlying `coweightMap`. -/
theorem coweightEquiv_autCongr_apply (e : P.Equiv Q) (g : Aut P) (y : N₂) :
    RootPairing.Equiv.coweightEquiv (e.autCongr g) y =
      e.coweightEquiv.symm (g.coweightEquiv (e.coweightEquiv y)) :=
  (rfl)

/-- The index permutation of a conjugated automorphism is the conjugated index permutation. -/
@[simp]
theorem indexEquiv_autCongr_apply (e : P.Equiv Q) (g : Aut P) (i : ι₂) :
    (e.autCongr g).indexEquiv i = e.indexEquiv (g.indexEquiv (e.indexEquiv.symm i)) :=
  (rfl)

/-- Conjugation transports the action on weight vectors along `e.weightEquiv`.

Not a `simp` lemma: `RootPairing.Equiv.weightEquiv_apply` rewrites `e.weightEquiv x` in the
left-hand side to `(↑e).weightMap x`, so the statement is not in `simp`-normal form. -/
theorem autCongr_smul (e : P.Equiv Q) (g : Aut P) (x : M) :
    e.autCongr g • e.weightEquiv x = e.weightEquiv (g • x) := by
  have h : e.autCongr g • e.weightEquiv x = weightEquiv (e.autCongr g) (e.weightEquiv x) := (rfl)
  have h' : g • x = g.weightEquiv x := (rfl)
  rw [h, h', RootPairing.Equiv.weightEquiv_autCongr_apply, LinearEquiv.symm_apply_apply]

/-- Conjugation transports the action on root indices along `e.indexEquiv`. -/
@[simp]
theorem autCongr_smul_index (e : P.Equiv Q) (g : Aut P) (i : ι) :
    e.autCongr g • e.indexEquiv i = e.indexEquiv (g • i) := by
  rw [RootPairing.Equiv.smul_index_eq_indexEquiv, RootPairing.Equiv.smul_index_eq_indexEquiv,
    RootPairing.Equiv.indexEquiv_autCongr_apply, Equiv.symm_apply_apply]

/-- An equivalence intertwining `σ` and `σ₂` via `e.autCongr σ = σ₂` intertwines their root-index
permutations. -/
theorem indexEquiv_apply_of_autCongr_eq (e : P.Equiv Q) {σ : Aut P} {σ₂ : Aut Q}
    (h : e.autCongr σ = σ₂) (i : ι) :
    e.indexEquiv (σ.indexEquiv i) = σ₂.indexEquiv (e.indexEquiv i) := by
  rw [← h, indexEquiv_autCongr_apply, Equiv.symm_apply_apply]

/-- Conjugation by `e` maps `σ` to `τ` if and only if `e.weightEquiv` intertwines their
weight-space maps. -/
theorem autCongr_eq_iff_weightEquiv_comp_weightMap (e : P.Equiv Q) {σ : Aut P} {τ : Aut Q} :
    e.autCongr σ = τ ↔
      e.weightEquiv.toLinearMap ∘ₗ σ.weightMap = τ.weightMap ∘ₗ e.weightEquiv.toLinearMap := by
  refine ⟨fun h ↦ LinearMap.ext fun x ↦ ?_, fun h ↦ ?_⟩
  · have hx := e.autCongr_smul σ x
    rw [h] at hx
    exact hx.symm
  · refine Equiv.weightHom_injective Q (LinearEquiv.ext fun y ↦ ?_)
    have hy := LinearMap.congr_fun h (e.weightEquiv.symm y)
    simp only [LinearMap.comp_apply, LinearEquiv.coe_coe, LinearEquiv.apply_symm_apply,
      weightEquiv_apply] at hy
    rw [weightHom_apply, weightHom_apply, weightEquiv_autCongr_apply]
    simp only [weightEquiv_apply]
    exact hy

/-- Conjugation by the identity equivalence is the identity. -/
@[simp]
theorem autCongr_id :
    (RootPairing.Equiv.id P).autCongr = MulEquiv.refl (Aut P) :=
  MulEquiv.ext fun g ↦ by
    -- `RootPairing.Equiv.symm P P` and `RootPairing.Equiv.id P` are the inversion and the unit of
    -- the group `RootPairing.Equiv P P`, so the inverse of the identity is `inv_one`.
    have h : RootPairing.Equiv.symm P P (RootPairing.Equiv.id P) = RootPairing.Equiv.id P := inv_one
    rw [RootPairing.Equiv.autCongr_apply, h,
      RootPairing.Equiv.id_comp, RootPairing.Equiv.comp_id]
    rfl

/-- Conjugation by a composite is the composite of the conjugations. -/
@[simp]
theorem autCongr_comp (e : P.Equiv Q) (f : Q.Equiv S) :
    (RootPairing.Equiv.comp f e).autCongr = e.autCongr.trans f.autCongr :=
  MulEquiv.ext fun g ↦ by
    simp only [RootPairing.Equiv.autCongr_apply, MulEquiv.trans_apply,
      RootPairing.Equiv.symm_comp, RootPairing.Equiv.comp_assoc]

end Conjugation

section Intertwine

/-- When the roots of `P` span, a homomorphism intertwining `σ` and `τ` on root indices intertwines
their weight-space endomorphisms on all of `M`. -/
theorem _root_.RootPairing.Hom.weightMap_comp_of_indexEquiv [P.IsRootSystem] (f : P.Hom Q)
    {σ : Aut P} {τ : Aut Q}
    (h : ∀ j, f.indexEquiv (σ.indexEquiv j) = τ.indexEquiv (f.indexEquiv j)) :
    f.weightMap ∘ₗ σ.weightMap = τ.weightMap ∘ₗ f.weightMap := by
  refine LinearMap.ext_on_range (IsRootSystem.span_root_eq_top (P := P)) fun j ↦ ?_
  simp only [LinearMap.comp_apply, Hom.root_weightMap_apply P P j σ.toHom,
    Hom.root_weightMap_apply P Q _ f, Hom.root_weightMap_apply Q Q _ τ.toHom, h j]

/-- A homomorphism intertwining the weight-space endomorphisms of `σ` and `τ` intertwines their
index permutations. No spanning assumption is needed. -/
theorem _root_.RootPairing.Hom.indexEquiv_apply_of_weightMap_comp (f : P.Hom Q) {σ : Aut P}
    {τ : Aut Q} (hw : f.weightMap ∘ₗ σ.weightMap = τ.weightMap ∘ₗ f.weightMap) (j : ι) :
    f.indexEquiv (σ.indexEquiv j) = τ.indexEquiv (f.indexEquiv j) := by
  apply Q.root.injective
  simpa only [LinearMap.comp_apply, Hom.root_weightMap_apply P P j σ.toHom,
    Hom.root_weightMap_apply P Q _ f, Hom.root_weightMap_apply Q Q _ τ.toHom] using
    LinearMap.congr_fun hw (P.root j)

/-- When the roots of `P` span, an equivalence intertwining `σ` and `τ` on root indices intertwines
their weight-space endomorphisms along `e.weightEquiv`. -/
theorem weightEquiv_comp_weightMap_of_indexEquiv [P.IsRootSystem] (e : P.Equiv Q)
    {σ : Aut P} {τ : Aut Q}
    (h : ∀ j, e.indexEquiv (σ.indexEquiv j) = τ.indexEquiv (e.indexEquiv j)) :
    e.weightEquiv.toLinearMap ∘ₗ σ.weightMap = τ.weightMap ∘ₗ e.weightEquiv.toLinearMap :=
  (LinearMap.ext e.weightEquiv_apply : e.weightEquiv.toLinearMap = e.toHom.weightMap) ▸
    e.toHom.weightMap_comp_of_indexEquiv h

/-- An equivalence intertwining the weight-space endomorphisms of `σ` and `τ` along `e.weightEquiv`
intertwines their index permutations. No spanning assumption is needed. -/
theorem indexEquiv_apply_of_weightEquiv_comp_weightMap (e : P.Equiv Q) {σ : Aut P} {τ : Aut Q}
    (hw : e.weightEquiv.toLinearMap ∘ₗ σ.weightMap = τ.weightMap ∘ₗ e.weightEquiv.toLinearMap)
    (j : ι) : e.indexEquiv (σ.indexEquiv j) = τ.indexEquiv (e.indexEquiv j) :=
  e.toHom.indexEquiv_apply_of_weightMap_comp
    ((LinearMap.ext e.weightEquiv_apply : e.weightEquiv.toLinearMap = e.toHom.weightMap) ▸ hw) j

end Intertwine

section Pow

/-- The index permutation of a power of an automorphism is the power of its index permutation. -/
@[simp]
theorem indexEquiv_pow (σ : Aut P) (n : ℕ) : (σ ^ n).indexEquiv = σ.indexEquiv ^ n := by
  rw [← indexHom_apply, map_pow, indexHom_apply]

/-- The weight map of a product of automorphisms is the composite of their weight maps.

Not a `simp` lemma: `RootPairing.Equiv.mul_eq_comp` rewrites its left-hand side. -/
theorem weightMap_mul_apply (σ τ : Aut P) (x : M) :
    (σ * τ).toHom.weightMap x = σ.toHom.weightMap (τ.toHom.weightMap x) := by
  simp only [mul_eq_comp, toHom_comp, Hom.comp_weightMap_apply]

/-- The weight map of a power of an automorphism is the power of its weight map. -/
@[simp]
theorem weightMap_pow (σ : Aut P) (n : ℕ) : (σ ^ n).toHom.weightMap = σ.toHom.weightMap ^ n := by
  induction n with
  | zero => simp only [pow_zero, toHom_one, Hom.weightMap_one, Module.End.one_eq_id]
  | succ n ih => ext x; rw [pow_succ, weightMap_mul_apply, ih, pow_succ, mul_apply_eq_comp]

end Pow

end RootPairing.Equiv

namespace RootPairing
section MapDual

variable {ι ι₂ R M N M₂ : Type*} [CommRing R] [AddCommGroup M] [Module R M]
  [AddCommGroup N] [Module R N] [AddCommGroup M₂] [Module R M₂]
  (P : RootPairing ι R M N) (e : ι ≃ ι₂) (f : M ≃ₗ[R] M₂)

/-- Transport a root pairing along `e : ι ≃ ι₂` and `f : M ≃ₗ[R] M₂` onto `M₂` paired with its
linear dual `Module.Dual R M₂` by evaluation. -/
noncomputable def mapDual : RootPairing ι₂ R M₂ (Module.Dual R M₂) :=
  P.map e f (P.flip.toPerfPair.trans f.symm.dualMap)

instance [P.IsRootSystem] : (P.mapDual e f).IsRootSystem :=
  inferInstanceAs (P.map e f (P.flip.toPerfPair.trans f.symm.dualMap)).IsRootSystem

@[simp] theorem mapDual_toLinearMap : (P.mapDual e f).toLinearMap = Module.Dual.eval R M₂ := by
  ext x φ; simp [mapDual, RootPairing.map]
theorem mapDual_toLinearMap_apply (x : M₂) (φ : Module.Dual R M₂) :
    (P.mapDual e f).toLinearMap x φ = φ x := by simp
@[simp] theorem mapDual_root_apply (i : ι₂) :
    (P.mapDual e f).root i = f (P.root (e.symm i)) := by rfl
@[simp] theorem mapDual_coroot (i : ι₂) :
    (P.mapDual e f).coroot i = (P.coroot' (e.symm i)).comp f.symm.toLinearMap := by
  ext x; simp [mapDual, RootPairing.map, coroot']
theorem mapDual_coroot_apply (i : ι₂) (x : M₂) :
    (P.mapDual e f).coroot i x = P.coroot' (e.symm i) (f.symm x) := by simp

/-- The canonical equivalence of root pairings from `P` to `P.mapDual e f`. -/
noncomputable def equivMapDual : P.Equiv (P.mapDual e f) :=
  P.equivMap e f (P.flip.toPerfPair.trans f.symm.dualMap)

@[simp] theorem equivMapDual_weightMap : (P.equivMapDual e f).weightMap = f.toLinearMap :=
  LinearMap.ext (P.weightMap_equivMap_apply e f _)
@[simp] theorem equivMapDual_weightEquiv : (P.equivMapDual e f).weightEquiv = f :=
  P.weightEquiv_equivMap e f _
@[simp] theorem equivMapDual_coweightMap : (P.equivMapDual e f).coweightMap =
    (P.flip.toPerfPair.trans f.symm.dualMap).symm.toLinearMap :=
  LinearMap.ext (P.coweightMap_equivMap_apply e f _)
@[simp] theorem equivMapDual_indexEquiv : (P.equivMapDual e f).indexEquiv = e :=
  P.indexEquiv_equivMap e f _

end MapDual
end RootPairing
