/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.RepresentationTheory.ClassicalGroups.BrauerGenerators.Orthogonal.Harmonic
public import TauCeti.RepresentationTheory.ClassicalGroups.ExtremeShape

/-!
# The orthogonal shape spaces `E_λ`

Let `V = kⁿ` carry the coordinate dot product, so that the orthogonal group `O_n(k)` acts
diagonally on `V^{⊗d}`. For a Young tableau `t` of shape `λ ⊢ d`, Weyl's orthogonal analogue of
the Schur functor is the space of harmonic tensors in the image of the Young symmetrizer:

`E_t = c_t · V^{⊗d} ∩ H^d`,

where `H^d = TauCeti.harmonicTensors k n d` is the common kernel of the contractions. Both pieces
are stable under `O_n(k)`: the image of `c_t` because permuting tensor factors commutes with the
diagonal action, and `H^d` because the contractions do. So `E_t` is a subrepresentation of
`V^{⊗d}`, `TauCeti.YoungTableau.orthShapeSpace`. Over `ℂ` the admissible `E_λ` are the irreducible
representations of `O_n` that occur in `V^{⊗d}` for the first time in degree `d`, and Weyl's theorem
says `E_λ ≠ 0` exactly when the first two columns of `λ` have total length at most `n`
(`TauCeti.OrthAdmissible`). This file builds `E_t` and proves the parts of that picture that need
no Brauer duality:

* `E_t` depends on `t` only up to isomorphism: relabeling the tableau moves `E_t` by a
  permutation of the tensor factors, which is `O_n(k)`-equivariant and preserves `H^d`
  (`TauCeti.YoungTableau.orthShapeRepEquiv`);
* `E_t = 0` as soon as `λ` has more than `n` rows, since then already `c_t · V^{⊗d} = 0`
  (`TauCeti.YoungTableau.orthShapeSpace_eq_bot`);
* on at most one strand nothing is contracted, so `E_t` is the whole Weyl module;
* for a one-column shape every tensor in the image of `c_t` is alternating, hence harmonic, so
  `E_{(1ᵈ)}` is the Weyl module `⋀ᵈ V`, and it vanishes exactly when `λ` is not admissible
  (`TauCeti.YoungTableau.orthShapeSpace_eq_bot_iff_of_rowLen_le_one`);
* for a one-row shape and `n ≥ 2`, a nonzero isotropic vector `v` gives the nonzero harmonic
  symmetric tensor `v^{⊗d}`, while for `n ≤ 1` the space vanishes in degree at least `2`; with a
  square root of `-1` in `k` this is again the admissibility criterion
  (`TauCeti.YoungTableau.orthShapeSpace_eq_bot_iff_of_colLen_le_one`).

The admissibility criterion for a general shape, irreducibility, and the decomposition of `H^d`
need the double-centralizer theorem for the Brauer algebra and are not proved here.

## Main definitions

* `TauCeti.OrthAdmissible`: the admissibility of a shape for `O_n`, `λᵗ₁ + λᵗ₂ ≤ n`.
* `TauCeti.YoungTableau.orthShapeSpace`: the shape space `E_t`, a subrepresentation of the
  diagonal action of `O_n(k)` on `V^{⊗|λ|}`, with `orthShapeRep` the action on it.

## Main results

* `TauCeti.YoungTableau.orthShapeRepEquiv`: the shape spaces of two tableaux of the same shape are
  isomorphic representations of `O_n(k)`.
* `TauCeti.YoungTableau.orthShapeSpace_eq_bot`: `E_t = 0` when `λ` has more than `n` rows.
* `TauCeti.YoungTableau.orthShapeSpace_toSubmodule_of_rowLen_le_one`: for a one-column shape
  `E_t` is the whole Weyl module.
* `TauCeti.YoungTableau.orthShapeSpace_eq_bot_iff_of_rowLen_le_one` and
  `TauCeti.YoungTableau.orthShapeSpace_eq_bot_iff_of_colLen_le_one`: Weyl's vanishing criterion
  for one-column and one-row shapes.

## References

* R. Goodman and N. R. Wallach, *Symmetry, Representations, and Invariants*, Springer GTM 255
  (2009), §10.2.1 and §§10.2.4–10.2.5.
* H. Weyl, *The Classical Groups*, Princeton University Press (1939), Chapter V, §7.
-/

public section

open Matrix
open scoped TensorProduct

universe u

namespace TauCeti

/-- **Admissibility of a shape for the orthogonal group `O_n`**: the first two columns of `μ` have
total length at most `n`, that is `λᵗ₁ + λᵗ₂ ≤ n`. Over `ℂ` this is exactly when the orthogonal
shape space `TauCeti.YoungTableau.orthShapeSpace` of a `μ`-tableau is nonzero. It is stronger than
the condition `λᵗ₁ ≤ n` for `GL_n`: for `n = 2` the shape `(2, 2)` has two rows but is not
admissible. -/
def OrthAdmissible (n : ℕ) (μ : YoungDiagram) : Prop :=
  μ.colLen 0 + μ.colLen 1 ≤ n

theorem orthAdmissible_iff {n : ℕ} {μ : YoungDiagram} :
    OrthAdmissible n μ ↔ μ.colLen 0 + μ.colLen 1 ≤ n :=
  Iff.rfl

/-- An admissible shape has at most `n` rows. -/
theorem OrthAdmissible.colLen_zero_le {n : ℕ} {μ : YoungDiagram} (h : OrthAdmissible n μ) :
    μ.colLen 0 ≤ n :=
  le_trans (Nat.le_add_right _ _) h

/-- A shape with at most one column is admissible exactly when it has at most `n` rows: its
second column is empty. -/
theorem orthAdmissible_iff_of_rowLen_le_one {n : ℕ} {μ : YoungDiagram} (h : μ.rowLen 0 ≤ 1) :
    OrthAdmissible n μ ↔ μ.colLen 0 ≤ n := by
  have h1 : μ.colLen 1 = 0 := by
    by_contra hne
    have hmem : (0, 1) ∈ μ := μ.mem_iff_lt_colLen.mpr (Nat.pos_of_ne_zero hne)
    have := μ.mem_iff_lt_rowLen.mp hmem
    omega
  rw [orthAdmissible_iff, h1, add_zero]

/-- A shape with at most one row and at least two cells is admissible exactly when `2 ≤ n`: both
of its first two columns have length one. -/
theorem orthAdmissible_iff_of_colLen_le_one {n : ℕ} {μ : YoungDiagram} (h : μ.colLen 0 ≤ 1)
    (hcard : 2 ≤ μ.card) : OrthAdmissible n μ ↔ 2 ≤ n := by
  have hrow : 2 ≤ μ.rowLen 0 := YoungDiagram.card_eq_rowLen_of_colLen_le_one h ▸ hcard
  have h0 : μ.colLen 0 = 1 :=
    le_antisymm h (μ.mem_iff_lt_colLen.mp (μ.mem_iff_lt_rowLen.mpr (by omega)))
  have h1 : μ.colLen 1 = 1 :=
    le_antisymm (h0 ▸ μ.colLen_anti 0 1 zero_le_one)
      (μ.mem_iff_lt_colLen.mp (μ.mem_iff_lt_rowLen.mpr (by omega)))
  rw [orthAdmissible_iff, h0, h1]

namespace YoungTableau

variable (k : Type u) [CommRing k] [Algebra ℚ k] (n : ℕ) {μ : YoungDiagram}

/-! ## The shape space of a tableau -/

/-- **The orthogonal shape space** `E_t` of a `μ`-tableau `t`: the harmonic tensors in the image
of the Young symmetrizer `c_t` acting on `(kⁿ)^{⊗|μ|}`, a subrepresentation of the diagonal action
of the orthogonal group because both the image of `c_t` and the harmonic tensors are stable under
it. -/
noncomputable def orthShapeSpace (t : YoungTableau μ) :
    Subrepresentation ((stdOrthogonalRep k n).tensorPower μ.card) :=
  tensorPowerRange (stdOrthogonalRep k n) μ.card (youngSymmetrizerOver k t) ⊓
    harmonicTensorsSubrep k n μ.card

/-- The shape space is the intersection of the image of the Young symmetrizer with the harmonic
tensors. -/
theorem orthShapeSpace_def (t : YoungTableau μ) :
    orthShapeSpace k n t =
      tensorPowerRange (stdOrthogonalRep k n) μ.card (youngSymmetrizerOver k t) ⊓
        harmonicTensorsSubrep k n μ.card :=
  (rfl)

/-- The submodule underlying the shape space: the harmonic tensors in the range of the Young
symmetrizer acting on the tensor power. -/
@[simp]
theorem orthShapeSpace_toSubmodule (t : YoungTableau μ) :
    (orthShapeSpace k n t).toSubmodule =
      LinearMap.range (permTensorActionAlgHom k n μ.card (youngSymmetrizerOver k t)) ⊓
        harmonicTensors k n μ.card := by
  rw [orthShapeSpace, Subrepresentation.toSubmodule_inf, tensorPowerRange_toSubmodule,
    harmonicTensorsSubrep_toSubmodule, permTensorActionAlgHom_def, permTensorAction_def]

/-- The shape space is the harmonic part of the Weyl module of `t`, the `GL n k`-module cut out
by the same symmetrizer. -/
theorem orthShapeSpace_toSubmodule_eq_weylModule_inf (t : YoungTableau μ) :
    (orthShapeSpace k n t).toSubmodule =
      (weylModule k n t).toSubmodule ⊓ harmonicTensors k n μ.card := by
  rw [orthShapeSpace_toSubmodule, weylModule_toSubmodule]

variable {k n} in
/-- A tensor lies in the shape space exactly when it is in the image of the Young symmetrizer and
is harmonic. -/
theorem mem_orthShapeSpace {t : YoungTableau μ} {x : ⨂[k]^μ.card (Fin n → k)} :
    x ∈ orthShapeSpace k n t ↔
      x ∈ LinearMap.range (permTensorActionAlgHom k n μ.card (youngSymmetrizerOver k t)) ∧
        x ∈ harmonicTensors k n μ.card := by
  rw [← Subrepresentation.mem_toSubmodule, orthShapeSpace_toSubmodule, Submodule.mem_inf]

/-- The action of the orthogonal group on the shape space. -/
noncomputable abbrev orthShapeRep (t : YoungTableau μ) :
    Representation k (Matrix.orthogonalGroup (Fin n) k) (orthShapeSpace k n t).toSubmodule :=
  (orthShapeSpace k n t).toRepresentation

/-- The action on the shape space is the restriction of the diagonal action on the tensor
power. -/
@[simp]
theorem orthShapeRep_apply_coe (t : YoungTableau μ) (g : Matrix.orthogonalGroup (Fin n) k)
    (x : (orthShapeSpace k n t).toSubmodule) :
    ((orthShapeRep k n t g x : (orthShapeSpace k n t).toSubmodule) :
        ⨂[k]^μ.card (Fin n → k)) = (stdOrthogonalRep k n).tensorPower μ.card g x :=
  (rfl)

/-! ## Independence of the tableau -/

variable {k n}

/-- Relabeling the tableau by `σ` moves the shape space by the permutation of the tensor factors
that `σ` induces: it moves the Weyl module that way and preserves the harmonic tensors. -/
theorem orthShapeSpace_relabel (σ : Equiv.Perm (Fin μ.card)) (t : YoungTableau μ) :
    (orthShapeSpace k n (relabel σ t)).toSubmodule =
      (orthShapeSpace k n t).toSubmodule.map (permTensorAction k n μ.card σ) := by
  rw [orthShapeSpace_toSubmodule_eq_weylModule_inf, orthShapeSpace_toSubmodule_eq_weylModule_inf,
    weylModule_relabel, Submodule.map_inf _ (permTensorAction_apply k n μ.card σ ▸
      (PiTensorProduct.reindex k (fun _ : Fin μ.card => Fin n → k) σ).injective),
    map_permTensorAction_harmonicTensors]

/-- Permuting the tensor factors by `σ` as a linear equivalence from the shape space of `t` to
the shape space of the relabeled tableau `σt`. -/
noncomputable def orthShapeRelabelEquiv (σ : Equiv.Perm (Fin μ.card)) (t : YoungTableau μ) :
    (orthShapeSpace k n t).toSubmodule ≃ₗ[k] (orthShapeSpace k n (relabel σ t)).toSubmodule :=
  (PiTensorProduct.reindex k (fun _ : Fin μ.card => Fin n → k) σ).ofSubmodules _ _
    (by rw [orthShapeSpace_relabel σ t, permTensorAction_apply])

/-- The relabeling equivalence is induced by permuting the tensor factors. -/
@[simp]
theorem orthShapeRelabelEquiv_apply_coe (σ : Equiv.Perm (Fin μ.card)) (t : YoungTableau μ)
    (x : (orthShapeSpace k n t).toSubmodule) :
    ((orthShapeRelabelEquiv σ t x : (orthShapeSpace k n (relabel σ t)).toSubmodule) :
        ⨂[k]^μ.card (Fin n → k)) = permTensorAction k n μ.card σ x := by
  rw [permTensorAction_apply]
  rfl

/-- Permuting the tensor factors commutes with the diagonal action of the orthogonal group, so
it is an isomorphism of representations from the shape space of `t` to that of `σt`. -/
noncomputable def orthShapeRelabelRepEquiv (σ : Equiv.Perm (Fin μ.card)) (t : YoungTableau μ) :
    (orthShapeRep k n t).Equiv (orthShapeRep k n (relabel σ t)) :=
  Representation.Equiv.mk (orthShapeRelabelEquiv σ t) fun g => by
    ext x
    have h := LinearMap.congr_fun (PiTensorProduct.commute_reindexRepresentation_map k
      (Fin n → k) (Fin μ.card) σ (stdOrthogonalRep k n g)) (x : ⨂[k]^μ.card (Fin n → k))
    simp only [mul_apply_eq_comp] at h
    simpa only [LinearMap.coe_comp, Function.comp_apply, LinearEquiv.coe_coe,
      orthShapeRelabelEquiv_apply_coe, orthShapeRep_apply_coe, Representation.tensorPower_apply,
      permTensorAction_apply, PiTensorProduct.reindexRepresentation_apply] using h

/-- The relabeling isomorphism of representations is induced by permuting the tensor factors. -/
@[simp]
theorem orthShapeRelabelRepEquiv_apply_coe (σ : Equiv.Perm (Fin μ.card)) (t : YoungTableau μ)
    (x : (orthShapeSpace k n t).toSubmodule) :
    ((orthShapeRelabelRepEquiv σ t x : (orthShapeSpace k n (relabel σ t)).toSubmodule) :
        ⨂[k]^μ.card (Fin n → k)) = permTensorAction k n μ.card σ x :=
  orthShapeRelabelEquiv_apply_coe σ t x

/-- The shape spaces of two tableaux of the same shape are isomorphic representations of the
orthogonal group: up to isomorphism `E_t` depends only on the shape of `t`. -/
noncomputable def orthShapeRepEquiv (t t' : YoungTableau μ) :
    (orthShapeRep k n t).Equiv (orthShapeRep k n t') :=
  relabel_relabelPerm t t' ▸ orthShapeRelabelRepEquiv (relabelPerm t t') t

/-- The isomorphism between the shape spaces of `t` and `t'` permutes the tensor factors by the
permutation `TauCeti.YoungTableau.relabelPerm t t'` carrying `t` to `t'`. -/
@[simp]
theorem orthShapeRepEquiv_apply_coe (t t' : YoungTableau μ)
    (x : (orthShapeSpace k n t).toSubmodule) :
    ((orthShapeRepEquiv t t' x : (orthShapeSpace k n t').toSubmodule) :
        ⨂[k]^μ.card (Fin n → k)) = permTensorAction k n μ.card (relabelPerm t t') x := by
  have key : ∀ (σ : Equiv.Perm (Fin μ.card)) (s : YoungTableau μ) (hs : relabel σ t = s),
      ((hs ▸ orthShapeRelabelRepEquiv σ t : (orthShapeRep k n t).Equiv (orthShapeRep k n s)) x :
        ⨂[k]^μ.card (Fin n → k)) = permTensorAction k n μ.card σ x := by
    rintro σ _ rfl
    exact orthShapeRelabelRepEquiv_apply_coe σ t x
  exact key _ _ (relabel_relabelPerm t t')

/-- The shape spaces of two tableaux of the same shape have the same `Module.finrank`. -/
theorem finrank_orthShapeSpace_eq (t t' : YoungTableau μ) :
    Module.finrank k (orthShapeSpace k n t).toSubmodule =
      Module.finrank k (orthShapeSpace k n t').toSubmodule :=
  (orthShapeRepEquiv t t').toLinearEquiv.finrank_eq

/-! ## Vanishing and the boundary cases -/

/-- The shape space of a `μ`-tableau vanishes as soon as `μ` has more than `n` rows, because the
Weyl module containing it already does. -/
theorem orthShapeSpace_eq_bot (t : YoungTableau μ) (hn : n < μ.colLen 0) :
    orthShapeSpace k n t = ⊥ := by
  refine Subrepresentation.toSubmodule_injective ?_
  rw [orthShapeSpace_toSubmodule_eq_weylModule_inf, weylModule_eq_bot t hn,
    Subrepresentation.toSubmodule_bot, bot_inf_eq, Subrepresentation.toSubmodule_bot]

/-- On at most one strand there is nothing to contract, so the shape space is the whole Weyl
module. -/
theorem orthShapeSpace_toSubmodule_of_card_le_one (t : YoungTableau μ) (h : μ.card ≤ 1) :
    (orthShapeSpace k n t).toSubmodule = (weylModule k n t).toSubmodule := by
  rw [orthShapeSpace_toSubmodule_eq_weylModule_inf, harmonicTensors_eq_top_of_le_one h,
    inf_top_eq]

/-! ## One-column shapes -/

/-- On a shape with at most one column the Young symmetrizer is the antisymmetrization, whose
image consists of alternating tensors; these are harmonic, so the whole Weyl module is. -/
theorem weylModule_le_harmonicTensors_of_rowLen_le_one (t : YoungTableau μ)
    (h : μ.rowLen 0 ≤ 1) : (weylModule k n t).toSubmodule ≤ harmonicTensors k n μ.card := by
  have : Invertible (2 : ℚ) := invertibleOfNonzero (by norm_num)
  have : Invertible (2 : k) := by
    have h2 := Invertible.map (algebraMap ℚ k) (2 : ℚ)
    rwa [map_ofNat] at h2
  rw [weylModule_toSubmodule]
  rintro _ ⟨x, rfl⟩
  exact mem_harmonicTensors_of_forall_swap_eq_neg fun i j hij =>
    permTensorAction_swap_youngSymmetrizerOver_of_rowLen_le_one k n t h hij x

/-- **For a one-column shape the shape space is the whole Weyl module**, that is
`E_{(1ᵈ)} = ⋀ᵈ(kⁿ)` (`TauCeti.YoungTableau.weylRepEquivExtPowerRep`): alternating tensors are
harmonic. -/
theorem orthShapeSpace_toSubmodule_of_rowLen_le_one (t : YoungTableau μ) (h : μ.rowLen 0 ≤ 1) :
    (orthShapeSpace k n t).toSubmodule = (weylModule k n t).toSubmodule := by
  rw [orthShapeSpace_toSubmodule_eq_weylModule_inf]
  exact inf_eq_left.mpr (weylModule_le_harmonicTensors_of_rowLen_le_one t h)

/-- **Weyl's vanishing criterion for one-column shapes**: the shape space of a one-column shape
vanishes exactly when the shape is not admissible, that is, when it has more than `n` rows. -/
theorem orthShapeSpace_eq_bot_iff_of_rowLen_le_one [Nontrivial k] (t : YoungTableau μ)
    (h : μ.rowLen 0 ≤ 1) : orthShapeSpace k n t = ⊥ ↔ ¬OrthAdmissible n μ := by
  rw [orthAdmissible_iff_of_rowLen_le_one h, not_le, ← weylModule_eq_bot_iff (k := k) t,
    ← Subrepresentation.toSubmodule_injective.eq_iff,
    ← Subrepresentation.toSubmodule_injective.eq_iff,
    orthShapeSpace_toSubmodule_of_rowLen_le_one t h]
  simp only [Subrepresentation.toSubmodule_bot]

/-! ## One-row shapes -/

/-- **A one-row shape space is nonzero once `n ≥ 2`**, provided `k` has a square root `i` of
`-1`: the vector `v = e₀ + i e₁` is isotropic, so `v^{⊗d}` is harmonic, and it is symmetric, so the
symmetrizer sends it to `d! • v^{⊗d} ≠ 0`. -/
theorem orthShapeSpace_ne_bot_of_colLen_le_one [Nontrivial k] (t : YoungTableau μ)
    (h : μ.colLen 0 ≤ 1) (hn : 2 ≤ n) {i : k} (hi : i * i = -1) :
    orthShapeSpace k n t ≠ ⊥ := by
  have : CharZero k := charZero_of_injective_algebraMap (algebraMap ℚ k).injective
  let a : Fin n := ⟨0, by omega⟩
  let b : Fin n := ⟨1, by omega⟩
  have hab : a ≠ b := by simp [a, b, Fin.ext_iff]
  let v : Fin n → k := Pi.single a 1 + i • Pi.single b 1
  have hv : v ⬝ᵥ v = 0 := by
    simp [v, dotProduct_add, hab, hab.symm, hi]
  intro hbot
  have hmem : permTensorActionAlgHom k n μ.card (youngSymmetrizerOver k t)
      (PiTensorProduct.tprod k fun _ => v) ∈ orthShapeSpace k n t := by
    refine mem_orthShapeSpace.mpr ⟨LinearMap.mem_range_self _ _, ?_⟩
    rw [permTensorActionAlgHom_youngSymmetrizerOver_tprod_const_of_colLen_le_one k n t h]
    exact Submodule.smul_mem _ _ (tprod_mem_harmonicTensors fun _ _ _ => hv)
  rw [hbot, permTensorActionAlgHom_youngSymmetrizerOver_tprod_const_of_colLen_le_one k n t h]
    at hmem
  have hzero := congrArg (fun w => (tensorPowerBasis k n μ.card).repr w fun _ => a)
    ((Submodule.mem_bot k).mp hmem)
  simp [tensorPowerBasis_def, v, hab.symm, Nat.factorial_ne_zero] at hzero

/-- **Weyl's vanishing criterion for one-row shapes**, over a ring containing a square root of
`-1`: the shape space of a one-row shape vanishes exactly when the shape is not admissible. In
degree at least two that means `n ≤ 1`, where the line `k¹` carries no nonzero harmonic tensor
of degree two or more. -/
theorem orthShapeSpace_eq_bot_iff_of_colLen_le_one [Nontrivial k] (t : YoungTableau μ)
    (h : μ.colLen 0 ≤ 1) {i : k} (hi : i * i = -1) :
    orthShapeSpace k n t = ⊥ ↔ ¬OrthAdmissible n μ := by
  rcases le_or_gt μ.card 1 with hcard | hcard
  · -- in degree at most one the shape is also a single column
    exact orthShapeSpace_eq_bot_iff_of_rowLen_le_one t
      (le_trans (YoungDiagram.card_eq_rowLen_of_colLen_le_one h ▸ le_rfl) hcard)
  rw [orthAdmissible_iff_of_colLen_le_one h hcard, not_le]
  refine ⟨fun hbot => not_le.mp fun hn => orthShapeSpace_ne_bot_of_colLen_le_one t h hn hi hbot,
    fun hn => ?_⟩
  have hrow : 1 ≤ μ.colLen 0 := μ.mem_iff_lt_colLen.mp
    (μ.mem_iff_lt_rowLen.mpr (YoungDiagram.card_eq_rowLen_of_colLen_le_one h ▸ by omega))
  rcases Nat.lt_succ_iff.mp hn |>.lt_or_eq with hn0 | rfl
  · exact orthShapeSpace_eq_bot t (by omega)
  · refine Subrepresentation.toSubmodule_injective ?_
    rw [orthShapeSpace_toSubmodule_eq_weylModule_inf, harmonicTensors_one_eq_bot hcard, inf_bot_eq,
      Subrepresentation.toSubmodule_bot]

end YoungTableau

end TauCeti
