/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import Mathlib.Geometry.Group.WordMetric
public import TauCeti.Algebra.Module.Submodule.GroupAction
public import TauCeti.LinearAlgebra.Matrix.Cartan.Realization.Weyl
import TauCeti.LinearAlgebra.Dual.Contragredient

/-!
# The Weyl group of a Cartan realization: generators, word length, and lattice actions

Let `R : CartanRealization A H` be a realization of a matrix `A` with diagonal entries `2` over a
field `K`, with simple coroots `hᵢ ∈ H` and simple roots `αᵢ ∈ H*` paired by `αⱼ(hᵢ) = A i j`.
The simple reflections `R.simpleReflection hA i` of `Dual K H`, the dual simple reflections
`R.simpleCoreflection hA i` of `H`, and the Weyl group `R.weylGroup hA` they generate are defined
in `TauCeti.LinearAlgebra.Matrix.Cartan.Realization.Weyl`. This file develops the Weyl group as an
abstract group with its generating family.

The dual simple reflections fix the Cartan center `R.cartanCenter` pointwise. Linear independence
of the simple roots and coroots ensures that distinct indices yield distinct simple reflections
over any field (`R.weylSimple_injective`).

The Weyl group `R.weylGroup hA` (characterized as finite products of simple reflections by
`R.mem_weylGroup_iff`) is packaged with a generating family `R.weylGenerators hA :
Group.Generators`, with word length `R.weylLength hA` given by Mathlib's
`Group.Generators.wordLength`. Without assuming finite dimensionality of `H` or finiteness of `I`,
the injective contragredient homomorphism `LinearEquiv.contragredientHom K H` matches each dual
simple reflection with the corresponding simple reflection. Inverting this isomorphism on the
generated subgroups yields a faithful ambient action
`R.ambientAction hA : R.weylGroup hA →* (H ≃ₗ[K] H)` preserving evaluation, fixing
`R.cartanCenter` pointwise, and stabilizing `R.corootSpan` together with every subspace containing
it.

For an integral matrix `A`, the Weyl group acts on the root lattice `R.rootLattice`, and for a
coweight lattice `L : R.CoweightLattice` of a rational realization it acts on both `L.lattice` and
`L.weightLattice` while preserving `L.pairing`. Finally, `R.weylGroup hA`, `R.weylLength hA`, and
the action on the root lattice are canonically invariant under linear equivalences `R.map e` and
under admissible restrictions `R.restrict M hc hs` (so enlarging a minimal realization by central
directions leaves the Weyl group and its root-lattice action unchanged).

## Main definitions

* `TauCeti.CartanRealization.weylSimple`: the `i`-th simple reflection as an element of
  `R.weylGroup hA`.
* `TauCeti.CartanRealization.weylGenerators`: the simple reflections as a `Group.Generators`
  family of `R.weylGroup hA`.
* `TauCeti.CartanRealization.ambientAction`: the contragredient action of `R.weylGroup hA` on
  `H`.
* `TauCeti.CartanRealization.weylLength`: the word-length function on `R.weylGroup hA`,
  abbreviating `(R.weylGenerators hA).wordLength`.
* `TauCeti.CartanRealization.rootLatticeAction`,
  `TauCeti.CartanRealization.CoweightLattice.coweightAction`,
  `TauCeti.CartanRealization.CoweightLattice.weightAction`: the induced integral actions on `Q`,
  `Y`, and `P`.
* `TauCeti.CartanRealization.mapWeylGroupEquiv`,
  `TauCeti.CartanRealization.restrictWeylGroupEquiv`: invariance under transport and central
  enlargement (intertwining `TauCeti.CartanRealization.restrictRootLatticeEquiv` via
  `TauCeti.CartanRealization.restrictRootLatticeEquiv_rootLatticeAction`).

## References

* V. G. Kac, *Infinite-dimensional Lie algebras*, third edition, §§3.7–3.11.
-/

public section

open Module

namespace TauCeti

namespace CartanRealization

section Reflections

variable {I K H : Type*} [Field K] [AddCommGroup H] [Module K H] {A : Matrix I I K}
  (R : CartanRealization A H) (hA : ∀ i, A i i = 2)

/-- The simple reflection is the `Module.reflection` in `αᵢ` along evaluation at `hᵢ`, for any
proof of `αᵢ(hᵢ) = 2`. -/
theorem simpleReflection_eq_reflection (i : I)
    (hf : Dual.eval K H (R.coroot i) (R.root i) = 2 := by simp [hA i]) :
    R.simpleReflection hA i = Module.reflection hf :=
  LinearEquiv.ext fun φ ↦ by rw [simpleReflection_apply, Module.reflection_apply, Dual.eval_apply]

/-- The dual simple reflection is the `Module.reflection` in `hᵢ` along `αᵢ`, for any proof of
`αᵢ(hᵢ) = 2`. -/
theorem simpleCoreflection_eq_reflection (i : I)
    (hf : R.root i (R.coroot i) = 2 := by simp [hA i]) :
    R.simpleCoreflection hA i = Module.reflection hf :=
  LinearEquiv.ext fun h ↦ by rw [simpleCoreflection_apply, Module.reflection_apply]

@[simp]
theorem simpleReflection_simpleReflection (i : I) (φ : Dual K H) :
    R.simpleReflection hA i (R.simpleReflection hA i φ) = φ := by
  rw [R.simpleReflection_eq_reflection hA i]
  exact Module.involutive_reflection _ φ

@[simp]
theorem simpleCoreflection_simpleCoreflection (i : I) (h : H) :
    R.simpleCoreflection hA i (R.simpleCoreflection hA i h) = h := by
  rw [R.simpleCoreflection_eq_reflection hA i]
  exact Module.involutive_reflection _ h

@[simp]
theorem simpleReflection_symm (i : I) :
    (R.simpleReflection hA i).symm = R.simpleReflection hA i := by
  rw [R.simpleReflection_eq_reflection hA i]
  exact Module.reflection_symm _

@[simp]
theorem simpleCoreflection_symm (i : I) :
    (R.simpleCoreflection hA i).symm = R.simpleCoreflection hA i := by
  rw [R.simpleCoreflection_eq_reflection hA i]
  exact Module.reflection_symm _

/-- A functional vanishing on `hᵢ` is fixed by the simple reflection `sᵢ`. -/
theorem simpleReflection_of_apply_coroot_eq_zero {i : I} {φ : Dual K H}
    (hφ : φ (R.coroot i) = 0) : R.simpleReflection hA i φ = φ := by
  rw [simpleReflection_apply, hφ, zero_smul, sub_zero]

/-- A vector annihilated by `αᵢ` is fixed by the dual simple reflection `sᵢ`. -/
theorem simpleCoreflection_of_root_apply_eq_zero {i : I} {h : H} (hh : R.root i h = 0) :
    R.simpleCoreflection hA i h = h := by
  rw [simpleCoreflection_apply, hh, zero_smul, sub_zero]

/-- Every dual simple reflection fixes the Cartan center pointwise. -/
theorem simpleCoreflection_of_mem_cartanCenter (i : I) {h : H} (hh : h ∈ R.cartanCenter) :
    R.simpleCoreflection hA i h = h :=
  R.simpleCoreflection_of_root_apply_eq_zero hA ((R.mem_cartanCenter_iff h).mp hh i)

private theorem contragredientHom_simpleCoreflection (i : I) :
    LinearEquiv.contragredientHom K H (R.simpleCoreflection hA i) = R.simpleReflection hA i := by
  rw [LinearEquiv.contragredientHom_apply, simpleCoreflection_symm, dualMap_simpleCoreflection]

/-- No dual simple reflection is the identity. -/
@[simp]
theorem simpleCoreflection_ne_one (i : I) : R.simpleCoreflection hA i ≠ 1 := by
  intro h
  obtain ⟨x, hx⟩ : ∃ x : H, R.root i x ≠ 0 :=
    not_forall.mp fun hall ↦ R.root_linearIndependent.ne_zero i (LinearMap.ext hall)
  have h1 : x - R.root i x • R.coroot i = x := by
    simpa [simpleCoreflection_apply] using congr($(h) x)
  exact smul_ne_zero hx (R.coroot_linearIndependent.ne_zero i) (sub_eq_self.mp h1)

/-- No simple reflection is the identity. -/
@[simp]
theorem simpleReflection_ne_one (i : I) : R.simpleReflection hA i ≠ 1 := fun h ↦
  R.simpleCoreflection_ne_one hA i <| LinearEquiv.contragredientHom_injective K H <| by
    rw [R.contragredientHom_simpleCoreflection hA i, map_one, h]

/-- Distinct indices determine distinct dual simple reflections over any field. -/
theorem simpleCoreflection_injective : Function.Injective (R.simpleCoreflection hA) := by
  intro i j h
  obtain ⟨x, hx⟩ : ∃ x : H, R.root i x ≠ 0 :=
    not_forall.mp fun hall ↦ R.root_linearIndependent.ne_zero i (LinearMap.ext hall)
  have h1 : x - R.root i x • R.coroot i = x - R.root j x • R.coroot j := by
    simpa [simpleCoreflection_apply] using congr($(h) x)
  have hsmul : R.root i x • R.coroot i = R.root j x • R.coroot j := sub_right_inj.mp h1
  have hsingle : Finsupp.single i (R.root i x) = Finsupp.single j (R.root j x) :=
    R.coroot_linearIndependent <| by simpa [Finsupp.linearCombination_single] using hsmul
  by_contra hij
  exact hx <| by simpa [Finsupp.single_apply, Ne.symm hij] using congr($(hsingle) i)

/-- Distinct indices determine distinct simple reflections over any field. -/
theorem simpleReflection_injective : Function.Injective (R.simpleReflection hA) :=
  fun i j h ↦ R.simpleCoreflection_injective hA <| LinearEquiv.contragredientHom_injective K H <| by
    rw [R.contragredientHom_simpleCoreflection hA i, R.contragredientHom_simpleCoreflection hA j, h]

@[simp]
theorem orderOf_simpleReflection (i : I) : orderOf (R.simpleReflection hA i) = 2 :=
  orderOf_eq_prime (R.simpleReflection_mul_self hA i ▸ sq _) (R.simpleReflection_ne_one hA i)

@[simp]
theorem orderOf_simpleCoreflection (i : I) : orderOf (R.simpleCoreflection hA i) = 2 :=
  orderOf_eq_prime (R.simpleCoreflection_mul_self hA i ▸ sq _)
    (R.simpleCoreflection_ne_one hA i)

/-- If `A i j = 0` and `A j i = 0`, the simple reflections `sᵢ` and `sⱼ` commute. -/
theorem commute_simpleReflection_of_eq_zero {i j : I} (hij : A i j = 0) (hji : A j i = 0) :
    Commute (R.simpleReflection hA i) (R.simpleReflection hA j) := by
  ext φ h
  simp only [mul_apply_eq_comp, simpleReflection_apply, map_sub, map_smul, root_coroot,
    hij, hji, zero_smul, sub_zero]
  exact sub_right_comm _ _ _

/-- If `A i j = 0` and `A j i = 0`, the dual simple reflections `sᵢ` and `sⱼ` commute. -/
theorem commute_simpleCoreflection_of_eq_zero {i j : I} (hij : A i j = 0) (hji : A j i = 0) :
    Commute (R.simpleCoreflection hA i) (R.simpleCoreflection hA j) := by
  ext h
  simp only [mul_apply_eq_comp, simpleCoreflection_apply, map_sub, map_smul, root_coroot,
    hij, hji, zero_smul, sub_zero]
  exact sub_right_comm _ _ _

/-! ### The Weyl group and its contragredient ambient action -/

/-- The `i`-th simple reflection as an element of the Weyl group. -/
noncomputable def weylSimple (i : I) : R.weylGroup hA :=
  ⟨R.simpleReflection hA i, R.simpleReflection_mem_weylGroup hA i⟩

@[simp]
theorem coe_weylSimple (i : I) :
    (R.weylSimple hA i : Dual K H ≃ₗ[K] Dual K H) = R.simpleReflection hA i := (rfl)

/-- The difference between the actions of `v` and `v * sᵢ` on a weight `lam` is the translated
simple root scaled by the value of `lam` on the simple coroot. -/
theorem smul_sub_mul_weylSimple_smul (v : R.weylGroup hA) (i : I) (lam : Dual K H) :
    v • lam - (v * R.weylSimple hA i) • lam = lam (R.coroot i) • (v • R.root i) := by
  simp [mul_smul, Subgroup.smul_def, coe_weylSimple, simpleReflection_apply]

@[simp]
theorem weylSimple_mul_self (i : I) :
    R.weylSimple hA i * R.weylSimple hA i = 1 :=
  Subtype.ext (R.simpleReflection_mul_self hA i)

@[simp]
theorem weylSimple_inv (i : I) :
    (R.weylSimple hA i)⁻¹ = R.weylSimple hA i :=
  Subtype.ext (R.simpleReflection_inv hA i)

/-- No simple reflection in the Weyl group is the identity. -/
@[simp]
theorem weylSimple_ne_one (i : I) : R.weylSimple hA i ≠ 1 := fun h ↦
  R.simpleReflection_ne_one hA i (congrArg Subtype.val h)

/-- Distinct indices determine distinct simple reflections in the Weyl group over any field. -/
theorem weylSimple_injective : Function.Injective (R.weylSimple hA) := fun _ _ h ↦
  R.simpleReflection_injective hA (congrArg Subtype.val h)

@[simp]
theorem orderOf_weylSimple (i : I) : orderOf (R.weylSimple hA i) = 2 :=
  orderOf_eq_prime (R.weylSimple_mul_self hA i ▸ sq _) (R.weylSimple_ne_one hA i)

/-- If `A i j = 0` and `A j i = 0`, the simple reflections `sᵢ` and `sⱼ` commute in the Weyl
group. -/
theorem commute_weylSimple_of_eq_zero {i j : I} (hij : A i j = 0) (hji : A j i = 0) :
    Commute (R.weylSimple hA i) (R.weylSimple hA j) :=
  Subtype.ext (R.commute_simpleReflection_of_eq_zero hA hij hji)

/-- The simple reflections generate the Weyl group. -/
theorem closure_range_weylSimple : Subgroup.closure (Set.range (R.weylSimple hA)) = ⊤ := by
  rw [eq_top_iff]
  rintro ⟨w, hw⟩ -
  have hw' : w ∈ Subgroup.closure (Set.range (R.simpleReflection hA)) := by
    rwa [← weylGroup_def]
  induction hw' using Subgroup.closure_induction with
  | mem x hx =>
    obtain ⟨i, rfl⟩ := hx
    exact Subgroup.subset_closure (Set.mem_range_self i)
  | one => exact one_mem _
  | mul _ _ hx hy ihx ihy =>
    exact mul_mem (ihx (by rwa [weylGroup_def])) (ihy (by rwa [weylGroup_def]))
  | inv _ hx ihx => exact inv_mem (ihx (by rwa [weylGroup_def]))

/-- The simple reflections as a `Group.Generators` family of the Weyl group. -/
noncomputable def weylGenerators : Group.Generators (R.weylGroup hA) I where
  val := R.weylSimple hA
  closure_eq_top := R.closure_range_weylSimple hA

/-- The generating family `R.weylGenerators hA` sends each index `i` to `R.weylSimple hA i`.
-/
@[simp]
theorem weylGenerators_val : (R.weylGenerators hA).val = R.weylSimple hA := (rfl)

/-- Induction on the Weyl group: because each simple reflection is its own inverse, closure under
`1`, the simple reflections, and multiplication suffices. -/
theorem weylGroup_induction {P : R.weylGroup hA → Prop} (one : P 1)
    (simple : ∀ i, P (R.weylSimple hA i)) (mul : ∀ u v, P u → P v → P (u * v))
    (w : R.weylGroup hA) : P w := by
  have hw : w ∈ Subgroup.closure (Set.range (R.weylSimple hA)) :=
    (R.closure_range_weylSimple hA).symm ▸ Subgroup.mem_top w
  induction hw using Subgroup.closure_induction'' with
  | one => exact one
  | mem _ h =>
    obtain ⟨i, rfl⟩ := h
    exact simple i
  | inv_mem _ h =>
    obtain ⟨i, rfl⟩ := h
    simpa using simple i
  | mul _ _ _ _ ih₁ ih₂ => exact mul _ _ ih₁ ih₂

/-- An ambient linear equivalence belongs to `R.weylGroup hA` if and only if it is the product
of a finite list of simple reflections. -/
theorem mem_weylGroup_iff {g : Dual K H ≃ₗ[K] Dual K H} :
    g ∈ R.weylGroup hA ↔ ∃ l : List I, (l.map (R.simpleReflection hA)).prod = g := by
  constructor
  · intro hg
    refine R.weylGroup_induction hA
      (P := fun w ↦ ∃ l : List I, (l.map (R.simpleReflection hA)).prod =
        (w : Dual K H ≃ₗ[K] Dual K H))
      ⟨[], by simp⟩ (fun i ↦ ⟨[i], by simp⟩)
      (fun u v ⟨l₁, hl₁⟩ ⟨l₂, hl₂⟩ ↦ ⟨l₁ ++ l₂, by simp [hl₁, hl₂]⟩) ⟨g, hg⟩
  · rintro ⟨l, rfl⟩
    exact list_prod_mem fun _ hx ↦ by
      obtain ⟨i, -, rfl⟩ := List.mem_map.mp hx
      exact R.simpleReflection_mem_weylGroup hA i

/-- Two homomorphisms out of the Weyl group agree if they agree on all simple reflections. -/
theorem weylGroup_hom_ext {G : Type*} [Monoid G] {f g : R.weylGroup hA →* G}
    (h : ∀ i, f (R.weylSimple hA i) = g (R.weylSimple hA i)) : f = g :=
  (R.weylGenerators hA).hom_ext f g h

/-- With an empty index set, the Weyl group is trivial. -/
instance [IsEmpty I] : Subsingleton (R.weylGroup hA) := by
  have eq_one : ∀ w : R.weylGroup hA, w = 1 :=
    R.weylGroup_induction hA (P := fun w ↦ w = 1) rfl isEmptyElim
      (fun _ _ h₁ h₂ ↦ by rw [h₁, h₂, mul_one])
  exact ⟨fun u v ↦ (eq_one u).trans (eq_one v).symm⟩

private theorem map_contragredientHom_closure_simpleCoreflection :
    (Subgroup.closure (Set.range (R.simpleCoreflection hA))).map
      (LinearEquiv.contragredientHom K H) = R.weylGroup hA := by
  rw [MonoidHom.map_closure, ← Set.range_comp, weylGroup_def]
  exact congrArg Subgroup.closure (congrArg Set.range
    (funext (R.contragredientHom_simpleCoreflection hA)))

/-- The faithful contragredient action of the Weyl group on the ambient space `H`, sending each
simple reflection `sᵢ` to the dual simple reflection `sᵢ` on `H`. No finite-dimensionality
assumption on `H` is needed. -/
noncomputable def ambientAction : R.weylGroup hA →* (H ≃ₗ[K] H) :=
  (Subgroup.closure (Set.range (R.simpleCoreflection hA))).subtype.comp
    ((Subgroup.equivMapOfInjective _ (LinearEquiv.contragredientHom K H)
      (LinearEquiv.contragredientHom_injective K H)).trans
      (MulEquiv.subgroupCongr
        (R.map_contragredientHom_closure_simpleCoreflection hA))).symm.toMonoidHom

/-- The dual action of `R.weylGroup hA` is precomposition with the inverse of
`R.ambientAction hA`. -/
@[simp]
theorem ambientAction_symm_dualMap (w : R.weylGroup hA) :
    (R.ambientAction hA w).symm.dualMap = (w : Dual K H ≃ₗ[K] Dual K H) := by
  let e := (Subgroup.equivMapOfInjective (Subgroup.closure (Set.range (R.simpleCoreflection hA)))
    (LinearEquiv.contragredientHom K H) (LinearEquiv.contragredientHom_injective K H)).trans
    (MulEquiv.subgroupCongr (R.map_contragredientHom_closure_simpleCoreflection hA))
  have h : LinearEquiv.contragredientHom K H (R.ambientAction hA w) =
      (w : Dual K H ≃ₗ[K] Dual K H) := congrArg Subtype.val (e.apply_symm_apply w)
  rwa [LinearEquiv.contragredientHom_apply] at h

/-- The ambient action of the `i`-th simple reflection is the `i`-th dual simple reflection. -/
@[simp]
theorem ambientAction_weylSimple (i : I) :
    R.ambientAction hA (R.weylSimple hA i) = R.simpleCoreflection hA i :=
  LinearEquiv.contragredientHom_injective K H <| by
    rw [LinearEquiv.contragredientHom_apply, R.ambientAction_symm_dualMap, coe_weylSimple,
      R.contragredientHom_simpleCoreflection]

/-- The contragredient action of the Weyl group on the ambient space `H` is faithful. -/
theorem ambientAction_injective : Function.Injective (R.ambientAction hA) := fun u v h ↦
  Subtype.ext <| by
    rw [← R.ambientAction_symm_dualMap hA u, ← R.ambientAction_symm_dualMap hA v, h]

/-- Every element of the Weyl group preserves the evaluation pairing with `H`:
`(w φ)(w h) = φ(h)`. -/
@[simp]
theorem apply_ambientAction (w : R.weylGroup hA) (φ : Dual K H) (h : H) :
    (w : Dual K H ≃ₗ[K] Dual K H) φ (R.ambientAction hA w h) = φ h := by
  rw [← R.ambientAction_symm_dualMap hA w, LinearEquiv.dualMap_apply,
    LinearEquiv.symm_apply_apply]

/-- Evaluating `w φ` on `h` is evaluating `φ` on `w⁻¹ h`. -/
theorem weylGroup_apply_apply (w : R.weylGroup hA) (φ : Dual K H) (h : H) :
    (w : Dual K H ≃ₗ[K] Dual K H) φ h = φ (R.ambientAction hA w⁻¹ h) := by
  rw [← R.ambientAction_symm_dualMap hA w, LinearEquiv.dualMap_apply, map_inv,
    LinearEquiv.coe_inv]

/-- **The Weyl group fixes the Cartan center pointwise.** -/
theorem ambientAction_of_mem_cartanCenter (w : R.weylGroup hA) {h : H}
    (hh : h ∈ R.cartanCenter) : R.ambientAction hA w h = h := by
  refine R.weylGroup_induction hA (P := fun w ↦ R.ambientAction hA w h = h)
    (by simp) (fun i ↦ ?_) (fun u v ihu ihv ↦ ?_) w
  · rw [ambientAction_weylSimple]
    exact R.simpleCoreflection_of_mem_cartanCenter hA i hh
  · rw [map_mul, mul_apply_eq_comp, ihv, ihu]

/-- On vectors in the Cartan center, every functional takes the same value before and after a
Weyl-group element acts. -/
theorem weylGroup_apply_of_mem_cartanCenter (w : R.weylGroup hA) (φ : Dual K H) {h : H}
    (hh : h ∈ R.cartanCenter) : (w : Dual K H ≃ₗ[K] Dual K H) φ h = φ h := by
  rw [R.weylGroup_apply_apply hA, R.ambientAction_of_mem_cartanCenter hA w⁻¹ hh]

/-- Every subspace of `H` containing the coroot span is stable under the Weyl group. -/
theorem ambientAction_mem_of_corootSpan_le {M : Submodule K H} (hc : R.corootSpan ≤ M)
    (w : R.weylGroup hA) {h : H} (hh : h ∈ M) : R.ambientAction hA w h ∈ M := by
  refine R.weylGroup_induction hA
    (P := fun w ↦ ∀ x : H, x ∈ M → R.ambientAction hA w x ∈ M)
    (fun x hx ↦ by simpa using hx) (fun i x hx ↦ ?_)
    (fun _ _ ihu ihv x hx ↦ by
      rw [map_mul, mul_apply_eq_comp]
      exact ihu _ (ihv x hx)) w h hh
  rw [ambientAction_weylSimple, simpleCoreflection_apply]
  exact sub_mem hx (Submodule.smul_mem _ _ (hc (R.coroot_mem_corootSpan i)))

/-- **The Weyl group stabilizes the coroot span.** -/
theorem ambientAction_mem_corootSpan (w : R.weylGroup hA) {h : H} (hh : h ∈ R.corootSpan) :
    R.ambientAction hA w h ∈ R.corootSpan :=
  R.ambientAction_mem_of_corootSpan_le hA le_rfl w hh

/-! ### Word length on the Weyl group -/

/-- Because every simple reflection is an involution, evaluating a signed word over
`R.weylGenerators hA` ignores the signs and multiplies the corresponding simple reflections. -/
@[simp]
theorem weylGenerators_wordProd (l : List (I × Bool)) :
    (R.weylGenerators hA).wordProd l = (l.map fun x ↦ R.weylSimple hA x.1).prod := by
  induction l with
  | nil => simp
  | cons x l ih =>
    rcases x with ⟨i, b⟩
    rw [Group.Generators.wordProd_cons, ih, List.map_cons, List.prod_cons, weylGenerators_val]
    cases b <;> simp

/-- The **word length** `ℓ(w)` of an element of the Weyl group, given by Mathlib's
`Group.Generators.wordLength` on `R.weylGenerators hA`. -/
noncomputable abbrev weylLength (w : R.weylGroup hA) : ℕ :=
  (R.weylGenerators hA).wordLength w

/-- The word length of `w` is at most `n` if and only if `w` is the product of at most `n` simple
reflections. -/
theorem weylLength_le_iff {w : R.weylGroup hA} {n : ℕ} :
    R.weylLength hA w ≤ n ↔
      ∃ l : List I, l.length ≤ n ∧ (l.map (R.weylSimple hA)).prod = w := by
  rw [Group.Generators.wordLength_le_iff]
  constructor
  · rintro ⟨l, hl, rfl⟩
    refine ⟨l.map Prod.fst, by simpa using hl, ?_⟩
    rw [List.map_map, weylGenerators_wordProd]
    rfl
  · rintro ⟨l, hl, rfl⟩
    refine ⟨l.map (·, true), by simpa using hl, ?_⟩
    rw [weylGenerators_wordProd, List.map_map]
    rfl

/-- Any word spelling `w` has length at least `R.weylLength hA w`. -/
theorem weylLength_le_of_prod_eq {l : List I} {w : R.weylGroup hA}
    (hl : (l.map (R.weylSimple hA)).prod = w) : R.weylLength hA w ≤ l.length :=
  (R.weylLength_le_iff hA).mpr ⟨l, le_rfl, hl⟩

/-- Every element of the Weyl group is represented by a list of simple reflections attaining its
`weylLength`. -/
theorem exists_length_eq_weylLength (w : R.weylGroup hA) :
    ∃ l : List I, l.length = R.weylLength hA w ∧ (l.map (R.weylSimple hA)).prod = w := by
  obtain ⟨l, hlen, hl⟩ := (R.weylLength_le_iff hA (w := w)).mp le_rfl
  exact ⟨l, le_antisymm hlen (R.weylLength_le_of_prod_eq hA hl), hl⟩

/-- Every element of the Weyl group is a product of a list of simple reflections. -/
theorem exists_word_prod_eq (w : R.weylGroup hA) :
    ∃ l : List I, (l.map (R.weylSimple hA)).prod = w :=
  let ⟨l, _, hl⟩ := R.exists_length_eq_weylLength hA w
  ⟨l, hl⟩

/-- A list of indices multiplies to `w` in `R.weylGroup hA` exactly when the corresponding
linear equivalences multiply to `w` in `Dual K H ≃ₗ[K] Dual K H`. -/
theorem prod_map_weylSimple_eq_iff (l : List I) (w : R.weylGroup hA) :
    (l.map (R.weylSimple hA)).prod = w ↔
      (l.map (R.simpleReflection hA)).prod = (w : Dual K H ≃ₗ[K] Dual K H) := by
  rw [← Subtype.coe_inj]
  simp [Function.comp_def]

/-- Every simple reflection has word length `1`. -/
@[simp]
theorem weylLength_weylSimple (i : I) :
    R.weylLength hA (R.weylSimple hA i) = 1 := by
  refine le_antisymm (R.weylLength_le_of_prod_eq hA (l := [i]) (by simp)) ?_
  exact Nat.one_le_iff_ne_zero.mpr fun h ↦
    R.weylSimple_ne_one hA i ((Group.Generators.wordLength_eq_zero_iff _).mp h)

end Reflections

/-! ### Integral lattice stability -/

/-- Cast an integral diagonal condition `∀ i, A i i = 2` to `(A.map Int.cast) i i = 2`. -/
theorem diag_map_intCast {I K : Type*} [AddGroupWithOne K] {A : Matrix I I ℤ}
    (hA : ∀ i, A i i = 2) :
    ∀ i, (A.map (Int.cast : ℤ → K)) i i = 2 := fun i ↦ by
  simp [hA i]

section RootLattice

variable {I K H : Type*} [Field K] [AddCommGroup H] [Module K H] {A : Matrix I I ℤ}
  (R : CartanRealization (A.map (Int.cast : ℤ → K)) H)
  (hA : ∀ i, (A.map (Int.cast : ℤ → K)) i i = 2)

/-- The induced action of the Weyl group on the root lattice `Q` by `ℤ`-linear equivalences. -/
noncomputable def rootLatticeAction : R.weylGroup hA →* (R.rootLattice ≃ₗ[ℤ] R.rootLattice) :=
  R.rootLattice.restrictLinearEquivHom (R.weylGroup hA).subtype
    (fun w _ ↦ (R.apply_mem_rootLattice_iff_of_mem_weylGroup hA w.property).mpr)

@[simp]
theorem coe_rootLatticeAction_apply (w : R.weylGroup hA) (φ : R.rootLattice) :
    (R.rootLatticeAction hA w φ : Dual K H) = (w : Dual K H ≃ₗ[K] Dual K H) φ :=
  Submodule.coe_restrictLinearEquivHom_apply _ _ _ w φ

end RootLattice

namespace CoweightLattice

variable {I H : Type*} [AddCommGroup H] [Module ℚ H] {A : Matrix I I ℤ}
  {R : CartanRealization (A.map (Int.cast : ℤ → ℚ)) H}
  (L : R.CoweightLattice) (hA : ∀ i, (A.map (Int.cast : ℤ → ℚ)) i i = 2)

/-- **The Weyl group stabilizes the coweight lattice `Y`.** -/
theorem ambientAction_mem_lattice (w : R.weylGroup hA) {y : H} (hy : y ∈ L.lattice) :
    R.ambientAction hA w y ∈ L.lattice := by
  refine R.weylGroup_induction hA
    (P := fun w ↦ ∀ z : H, z ∈ L.lattice → R.ambientAction hA w z ∈ L.lattice)
    (fun z hz ↦ by simpa using hz) (fun i z hz ↦ ?_)
    (fun _ _ ihu ihv z hz ↦ by
      rw [map_mul, mul_apply_eq_comp]
      exact ihu _ (ihv z hz)) w y hy
  rw [R.ambientAction_weylSimple hA i]
  exact (L.simpleCoreflection_mem_lattice_iff hA i).mpr hz

/-- The induced action of the Weyl group on the coweight lattice `Y`. -/
noncomputable def coweightAction : R.weylGroup hA →* (L.lattice ≃ₗ[ℤ] L.lattice) :=
  L.lattice.restrictLinearEquivHom (R.ambientAction hA)
    (fun w _ ↦ L.ambientAction_mem_lattice hA w)

/-- The induced action of the Weyl group on the weight lattice `P`. -/
noncomputable def weightAction : R.weylGroup hA →* (L.weightLattice ≃ₗ[ℤ] L.weightLattice) :=
  L.weightLattice.restrictLinearEquivHom (R.weylGroup hA).subtype
    (fun w _ ↦ (L.apply_mem_weightLattice_iff_of_mem_weylGroup hA w.property).mpr)

@[simp]
theorem coe_coweightAction_apply (w : R.weylGroup hA) (y : L.lattice) :
    (L.coweightAction hA w y : H) = R.ambientAction hA w y :=
  Submodule.coe_restrictLinearEquivHom_apply _ _ _ w y

@[simp]
theorem coe_weightAction_apply (w : R.weylGroup hA) (φ : L.weightLattice) :
    (L.weightAction hA w φ : Dual ℚ H) = (w : Dual ℚ H ≃ₗ[ℚ] Dual ℚ H) φ :=
  Submodule.coe_restrictLinearEquivHom_apply _ _ _ w φ

/-- **The Weyl-group actions on `P` and `Y` preserve the perfect integral pairing.** -/
@[simp]
theorem pairing_weightAction_coweightAction (w : R.weylGroup hA) (φ : L.weightLattice)
    (y : L.lattice) :
    L.pairing (L.weightAction hA w φ) (L.coweightAction hA w y) = L.pairing φ y := by
  apply Int.cast_injective (α := ℚ)
  rw [L.cast_pairing, L.cast_pairing, coe_weightAction_apply, coe_coweightAction_apply,
    R.apply_ambientAction hA]

end CoweightLattice

/-! ### Invariance under transport and central enlargement -/

section Invariance

variable {I K H H' : Type*} [Field K] [AddCommGroup H] [Module K H]
  [AddCommGroup H'] [Module K H'] {A : Matrix I I K}
  (R : CartanRealization A H) (hA : ∀ i, A i i = 2)

/-- Transporting a realization along `e : H ≃ₗ[K] H'` conjugates each simple reflection by
`e.symm.dualMap`. -/
theorem map_simpleReflection (e : H ≃ₗ[K] H') (i : I) :
    (R.map e).simpleReflection hA i =
      e.dualMap.trans ((R.simpleReflection hA i).trans e.dualMap.symm) := by
  ext φ h'
  simp [simpleReflection_apply]

/-- Transporting a realization along `e : H ≃ₗ[K] H'` induces a canonical isomorphism of Weyl
groups sending simple reflections to simple reflections. -/
noncomputable def mapWeylGroupEquiv (e : H ≃ₗ[K] H') :
    R.weylGroup hA ≃* (R.map e).weylGroup hA := by
  let conj : (Dual K H ≃ₗ[K] Dual K H) ≃* (Dual K H' ≃ₗ[K] Dual K H') :=
    (LinearMap.GeneralLinearGroup.generalLinearEquiv K (Dual K H)).symm.trans <|
      (LinearMap.GeneralLinearGroup.congrLinearEquiv e.dualMap.symm).trans
        (LinearMap.GeneralLinearGroup.generalLinearEquiv K (Dual K H'))
  have hmap : (R.weylGroup hA).map (conj : _ →* _) = (R.map e).weylGroup hA := by
    rw [weylGroup_def, weylGroup_def, MonoidHom.map_closure, ← Set.range_comp]
    refine congrArg Subgroup.closure (congrArg Set.range (funext fun i ↦ ?_))
    exact (R.map_simpleReflection hA e i).symm
  exact (conj.subgroupMap (R.weylGroup hA)).trans (MulEquiv.subgroupCongr hmap)

@[simp]
theorem mapWeylGroupEquiv_apply_apply (e : H ≃ₗ[K] H') (w : R.weylGroup hA)
    (φ : Dual K H') :
    ((R.mapWeylGroupEquiv hA e w : Dual K H' ≃ₗ[K] Dual K H') φ) =
      e.symm.dualMap ((w : Dual K H ≃ₗ[K] Dual K H) (e.dualMap φ)) := by
  dsimp only [mapWeylGroupEquiv]
  rw [MulEquiv.trans_apply, MulEquiv.subgroupCongr_apply, MulEquiv.coe_subgroupMap_apply]
  simp [LinearMap.GeneralLinearGroup.generalLinearEquiv]

@[simp]
theorem mapWeylGroupEquiv_weylSimple (e : H ≃ₗ[K] H') (i : I) :
    R.mapWeylGroupEquiv hA e (R.weylSimple hA i) = (R.map e).weylSimple hA i :=
  Subtype.ext <| LinearEquiv.ext fun φ ↦ by
    simp [R.map_simpleReflection hA e i]

@[simp]
theorem mapWeylGroupEquiv_symm_weylSimple (e : H ≃ₗ[K] H') (i : I) :
    (R.mapWeylGroupEquiv hA e).symm ((R.map e).weylSimple hA i) =
      R.weylSimple hA i :=
  (R.mapWeylGroupEquiv hA e).symm_apply_eq.mpr (R.mapWeylGroupEquiv_weylSimple hA e i).symm

/-- Transporting along `e : H ≃ₗ[K] H'` intertwines the ambient actions of `R.weylGroup` and
`(R.map e).weylGroup`. -/
theorem ambientAction_mapWeylGroupEquiv (e : H ≃ₗ[K] H') (w : R.weylGroup hA) (h : H) :
    (R.map e).ambientAction hA (R.mapWeylGroupEquiv hA e w) (e h) =
      e (R.ambientAction hA w h) := by
  refine R.weylGroup_induction hA
    (P := fun w ↦ ∀ x : H, (R.map e).ambientAction hA (R.mapWeylGroupEquiv hA e w) (e x) =
      e (R.ambientAction hA w x))
    (fun x ↦ by simp) (fun i x ↦ ?_)
    (fun u v ihu ihv x ↦ by
      simp only [map_mul, mul_apply_eq_comp, ihv, ihu]) w h
  simp [simpleCoreflection_apply]

/-- Any isomorphism of Weyl groups matching simple reflections index-by-index preserves
`weylLength`, even across distinct scalar fields. -/
theorem weylLength_equiv {K' H'' : Type*} [Field K'] [AddCommGroup H''] [Module K' H'']
    {A' : Matrix I I K'} {R' : CartanRealization A' H''}
    (hA' : ∀ i, A' i i = 2) (e : R.weylGroup hA ≃* R'.weylGroup hA')
    (he : ∀ i, e (R.weylSimple hA i) = R'.weylSimple hA' i) (w : R.weylGroup hA) :
    R'.weylLength hA' (e w) = R.weylLength hA w := by
  have hcomp : e ∘ R.weylSimple hA = R'.weylSimple hA' := funext he
  have hle : R'.weylLength hA' (e w) ≤ R.weylLength hA w := by
    obtain ⟨l, hl, rfl⟩ := R.exists_length_eq_weylLength hA w
    refine hl ▸ R'.weylLength_le_of_prod_eq hA' (l := l) ?_
    rw [map_list_prod, List.map_map, hcomp]
  refine le_antisymm hle ?_
  obtain ⟨l, hl, hprod⟩ := R'.exists_length_eq_weylLength hA' (e w)
  refine hl ▸ R.weylLength_le_of_prod_eq hA (l := l) ?_
  apply e.injective
  rw [map_list_prod, List.map_map, hcomp]
  exact hprod

@[simp]
theorem weylLength_mapWeylGroupEquiv (e : H ≃ₗ[K] H') (w : R.weylGroup hA) :
    (R.map e).weylLength hA (R.mapWeylGroupEquiv hA e w) = R.weylLength hA w :=
  R.weylLength_equiv hA hA (R.mapWeylGroupEquiv hA e)
    (R.mapWeylGroupEquiv_weylSimple hA e) w

section Restrict

variable (M : Submodule K H) (hc : R.corootSpan ≤ M) (hs : M ⊔ R.cartanCenter = ⊤)

/-- Restricting the ambient action of `R.weylGroup hA` to an invariant subspace `M` containing
the coroot span. -/
private noncomputable def restrictAmbientHom : R.weylGroup hA →* (M ≃ₗ[K] M) :=
  M.restrictLinearEquivHom (R.ambientAction hA)
    (fun w _ ↦ R.ambientAction_mem_of_corootSpan_le hA hc w)

include hs in
private theorem restrictAmbientHom_injective :
    Function.Injective (R.restrictAmbientHom hA M hc) := by
  refine (injective_iff_map_eq_one _).mpr fun w hw ↦ R.ambientAction_injective hA ?_
  ext x
  have hx : x ∈ M ⊔ R.cartanCenter := hs ▸ Submodule.mem_top
  obtain ⟨m, hm, z, hz, rfl⟩ := Submodule.mem_sup.mp hx
  have hm' : R.ambientAction hA w m = m := by
    simpa [restrictAmbientHom] using congrArg Subtype.val congr($(hw) ⟨m, hm⟩)
  rw [map_add, hm', R.ambientAction_of_mem_cartanCenter hA w hz, map_one, one_apply_eq_self]

private theorem restrictAmbientHom_weylSimple (i : I) :
    R.restrictAmbientHom hA M hc (R.weylSimple hA i) =
      (R.restrict M hc hs).simpleCoreflection hA i := by
  ext m
  rw [restrictAmbientHom, Submodule.coe_restrictLinearEquivHom_apply,
    R.ambientAction_weylSimple hA i]
  simp [simpleCoreflection_apply]

/-- The contragredient of `R.restrictAmbientHom`, sending `R.weylGroup hA` injectively into
`Dual K M ≃ₗ[K] Dual K M`. -/
private noncomputable def restrictDualHom : R.weylGroup hA →* (Dual K M ≃ₗ[K] Dual K M) :=
  (LinearEquiv.contragredientHom K M).comp (R.restrictAmbientHom hA M hc)

private theorem restrictDualHom_weylSimple (i : I) :
    R.restrictDualHom hA M hc (R.weylSimple hA i) =
      (R.restrict M hc hs).simpleReflection hA i := by
  rw [restrictDualHom, MonoidHom.comp_apply, R.restrictAmbientHom_weylSimple hA M hc hs i,
    contragredientHom_simpleCoreflection]

private theorem range_restrictDualHom :
    (R.restrictDualHom hA M hc).range = (R.restrict M hc hs).weylGroup hA := by
  rw [MonoidHom.range_eq_map, ← R.closure_range_weylSimple hA, MonoidHom.map_closure,
    ← Set.range_comp, (R.restrict M hc hs).weylGroup_def]
  exact congrArg Subgroup.closure <| congrArg Set.range <| funext fun i ↦
    R.restrictDualHom_weylSimple hA M hc hs i

/-- **Invariance of the Weyl group under admissible restriction (and hence under central
enlargement).** If `M` contains the coroot span and spans `H` together with `R.cartanCenter`, then
the Weyl group of `R` is canonically isomorphic to the Weyl group of `R.restrict M hc hs`,
matching simple reflections index-by-index. -/
noncomputable def restrictWeylGroupEquiv :
    R.weylGroup hA ≃* (R.restrict M hc hs).weylGroup hA :=
  (MonoidHom.ofInjective (f := R.restrictDualHom hA M hc) <|
    (LinearEquiv.contragredientHom_injective K M).comp
      (R.restrictAmbientHom_injective hA M hc hs)).trans
    (MulEquiv.subgroupCongr (R.range_restrictDualHom hA M hc hs))

private theorem coe_restrictWeylGroupEquiv (w : R.weylGroup hA) :
    (R.restrictWeylGroupEquiv hA M hc hs w : Dual K M ≃ₗ[K] Dual K M) =
      R.restrictDualHom hA M hc w := (rfl)

@[simp]
theorem restrictWeylGroupEquiv_weylSimple (i : I) :
    R.restrictWeylGroupEquiv hA M hc hs (R.weylSimple hA i) =
      (R.restrict M hc hs).weylSimple hA i :=
  Subtype.ext <| (R.coe_restrictWeylGroupEquiv hA M hc hs _).trans
    (R.restrictDualHom_weylSimple hA M hc hs i)

@[simp]
theorem restrictWeylGroupEquiv_symm_weylSimple (i : I) :
    (R.restrictWeylGroupEquiv hA M hc hs).symm ((R.restrict M hc hs).weylSimple hA i) =
      R.weylSimple hA i :=
  (R.restrictWeylGroupEquiv hA M hc hs).symm_apply_eq.mpr
    (R.restrictWeylGroupEquiv_weylSimple hA M hc hs i).symm

/-- The ambient action of `(R.restrict M hc hs).weylGroup` on `M` is the restriction of
`R.ambientAction` to `M`. -/
@[simp]
theorem coe_ambientAction_restrictWeylGroupEquiv (w : R.weylGroup hA) (m : M) :
    (((R.restrict M hc hs).ambientAction hA
        (R.restrictWeylGroupEquiv hA M hc hs w) m : M) : H) =
      R.ambientAction hA w m := by
  have h : (R.restrict M hc hs).ambientAction hA
      (R.restrictWeylGroupEquiv hA M hc hs w) = R.restrictAmbientHom hA M hc w :=
    LinearEquiv.contragredientHom_injective K M <| by
      rw [LinearEquiv.contragredientHom_apply,
        (R.restrict M hc hs).ambientAction_symm_dualMap hA,
        R.coe_restrictWeylGroupEquiv hA M hc hs w, restrictDualHom, MonoidHom.comp_apply]
  rw [h, restrictAmbientHom, Submodule.coe_restrictLinearEquivHom_apply]

/-- Restriction of functionals to `M` intertwines the action of `R.weylGroup hA` on `Dual K H`
with the action of `(R.restrict M hc hs).weylGroup hA` on `Dual K M`. -/
theorem restrictWeylGroupEquiv_comp_subtype (w : R.weylGroup hA) (φ : Dual K H) :
    ((R.restrictWeylGroupEquiv hA M hc hs w : Dual K M ≃ₗ[K] Dual K M) (φ.comp M.subtype)) =
      ((w : Dual K H ≃ₗ[K] Dual K H) φ).comp M.subtype := by
  ext m
  rw [(R.restrict M hc hs).weylGroup_apply_apply hA, ← map_inv, LinearMap.comp_apply,
    Submodule.subtype_apply, R.coe_ambientAction_restrictWeylGroupEquiv hA M hc hs,
    LinearMap.comp_apply, Submodule.subtype_apply, R.weylGroup_apply_apply hA]

/-- **Word length is invariant under admissible restriction (and central enlargement).** -/
@[simp]
theorem weylLength_restrictWeylGroupEquiv (w : R.weylGroup hA) :
    (R.restrict M hc hs).weylLength hA (R.restrictWeylGroupEquiv hA M hc hs w) =
      R.weylLength hA w :=
  R.weylLength_equiv hA hA (R.restrictWeylGroupEquiv hA M hc hs)
    (R.restrictWeylGroupEquiv_weylSimple hA M hc hs) w

end Restrict

/-- For an integral matrix `A`, `R.restrictRootLatticeEquiv` intertwines the Weyl-group action on
`R.rootLattice` with the restricted Weyl-group action on `(R.restrict M hc hs).rootLattice`. -/
theorem restrictRootLatticeEquiv_rootLatticeAction {B : Matrix I I ℤ}
    (S : CartanRealization (B.map (Int.cast : ℤ → K)) H)
    (hB : ∀ i, (B.map (Int.cast : ℤ → K)) i i = 2)
    (M : Submodule K H) (hc : S.corootSpan ≤ M) (hs : M ⊔ S.cartanCenter = ⊤)
    (w : S.weylGroup hB) (φ : S.rootLattice) :
    S.restrictRootLatticeEquiv M hc hs (S.rootLatticeAction hB w φ) =
      (S.restrict M hc hs).rootLatticeAction hB
        (S.restrictWeylGroupEquiv hB M hc hs w) (S.restrictRootLatticeEquiv M hc hs φ) :=
  Subtype.ext <| by
    simp only [coe_restrictRootLatticeEquiv_apply, coe_rootLatticeAction_apply]
    exact (S.restrictWeylGroupEquiv_comp_subtype hB M hc hs w φ).symm

end Invariance

end CartanRealization

end TauCeti
