/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import Mathlib.GroupTheory.GroupAction.Quotient
public import TauCeti.FieldTheory.Galois.FixedField
public import TauCeti.FieldTheory.GaloisGroups.Orbits

/-!
# Point stabilizers of the Galois action on the roots

Let `p` be a polynomial over a field `F` and let `L = p.SplittingField`. The Galois group
`Polynomial.Gal p` acts on `p.rootSet L`, and this file identifies the stabilizer of a root `x`
with a relative Galois group: it is the subgroup of `p.Gal` fixing the simple extension `F⟮x⟯`
pointwise. The fixed-field and endpoint readings of the action against the Galois correspondence
go through that identification.

The identification itself needs no hypothesis on `p`. Recovering the fixed field and the two
ends of the Galois correspondence needs `IsGalois F L`. The index, however, is an
orbit-stabilizer calculation: it only needs the minimal polynomial of the chosen root to be
separable, and for irreducible `p` this follows from `p.Separable`.

## Main results

* `TauCeti.stabilizer_eq_fixingSubgroup_adjoin_simple`: the stabilizer of a root is the fixing
  subgroup of the field the root generates.
* `TauCeti.fixedField_stabilizer`: for a Galois splitting field, the field the stabilizer fixes
  is that same field.
* `TauCeti.index_stabilizer_eq_natDegree_minpoly`,
  `TauCeti.index_stabilizer_eq_natDegree`: the index of the stabilizer is the degree of the
  minimal polynomial of the root, so for irreducible separable `p` it is `p.natDegree`.
* `TauCeti.stabilizer_eq_bot_iff_adjoin_simple_eq_top`,
  `TauCeti.stabilizer_eq_top_iff_adjoin_simple_eq_bot`: the two ends of the correspondence, a
  root that generates the whole splitting field and a root that lies in the base field.
* `TauCeti.coe_rootSet_eq_orbit_of_irreducible`, `TauCeti.rootSetEquivQuotientStabilizer`: for the
  action of `Gal(M/F)` on the roots in a normal extension `M / F` of an irreducible polynomial,
  the roots form one orbit and are identified equivariantly with the cosets of the stabilizer of
  a chosen root `α`, the coset of `ρ` corresponding to the root `ρ • α`.

## Implementation notes

The action used here is Mathlib's `Polynomial.Gal.galActionAux`, the intrinsic action on
`p.rootSet p.SplittingField`, for which `↑(g • x)` is literally `g ↑x`. Mathlib also has
`Polynomial.Gal.galAction` on `p.rootSet E` for a splitting extension `E`, but its instance for
`E = p.SplittingField` is the transport of `galActionAux` along `Polynomial.Gal.rootsEquivRoots`,
which goes through the `Algebra p.SplittingField p.SplittingField` instance built from
`IsSplittingField.lift` rather than through the identity. The two actions are isomorphic but not
the same instance, and only the intrinsic one has stabilizers that the Galois correspondence
reads directly. No `Fact` instance is introduced below, so `galActionAux` is the only candidate
and no ambiguity arises.
-/

public section

namespace TauCeti

open Polynomial IntermediateField MulAction

variable {F : Type*} [Field F] {p : F[X]}

/-! ### The stabilizer of a root -/

/-- **The stabilizer of a root is a relative Galois group.** An automorphism of the splitting
field fixes a root `x` exactly when it fixes the subfield `F⟮x⟯` pointwise, so the point
stabilizer of the root action is the fixing subgroup of that subfield.

No hypothesis on `p` is needed: the statement is about one root and the field it generates, not
about the polynomial. -/
theorem stabilizer_eq_fixingSubgroup_adjoin_simple (x : p.rootSet p.SplittingField) :
    stabilizer p.Gal x = F⟮(x : p.SplittingField)⟯.fixingSubgroup := by
  ext σ
  rw [MulAction.mem_stabilizer_iff, Subtype.ext_iff, Polynomial.Gal.coe_smul,
    IntermediateField.fixingSubgroup_adjoin_simple]
  exact Iff.rfl

/-- **The field a root generates is recovered from its stabilizer.** When the splitting field is
Galois over `F` the fixed field of the stabilizer of `x` is `F⟮x⟯`. -/
theorem fixedField_stabilizer [IsGalois F p.SplittingField] (x : p.rootSet p.SplittingField) :
    IntermediateField.fixedField (stabilizer p.Gal x) = F⟮(x : p.SplittingField)⟯ := by
  rw [stabilizer_eq_fixingSubgroup_adjoin_simple, IsGalois.fixedField_fixingSubgroup]

/-! ### The index of a point stabilizer -/

/-- **The index of a point stabilizer is the degree of the minimal polynomial of the point.** The
orbit of `x` consists of all roots of its minimal polynomial in the normal splitting field, and
separability makes their number its degree, so this is orbit-stabilizer applied to
`TauCeti.natCard_orbit_eq_natDegree_minpoly_splittingField`. -/
theorem index_stabilizer_eq_natDegree_minpoly (x : p.rootSet p.SplittingField)
    (hsep : (minpoly F (x : p.SplittingField)).Separable) :
    (stabilizer p.Gal x).index = (minpoly F (x : p.SplittingField)).natDegree := by
  rw [MulAction.index_stabilizer, ← Nat.card_coe_set_eq,
    natCard_orbit_eq_natDegree_minpoly_splittingField x hsep]

/-- **For an irreducible separable polynomial every point stabilizer has index the degree.** This
is the form the permutation representation uses: a transitive subgroup of degree `n` has point
stabilizers of index `n`.

Separability cannot be dropped: an inseparable irreducible polynomial has fewer roots than its
degree. -/
theorem index_stabilizer_eq_natDegree (hp : Irreducible p) (hsep : p.Separable)
    (x : p.rootSet p.SplittingField) : (stabilizer p.Gal x).index = p.natDegree := by
  have := isPretransitive_of_irreducible hp
  rw [MulAction.index_stabilizer_of_transitive, Nat.card_eq_fintype_card,
    card_rootSet_eq_natDegree hsep (IsSplittingField.splits p.SplittingField p)]

/-! ### The two ends of the correspondence -/

/-- **A root with trivial stabilizer is a primitive element**, and conversely. Together with
`TauCeti.stabilizer_eq_top_iff_adjoin_simple_eq_bot` this pins the orientation of the
correspondence: the stabilizer shrinks as the field the root generates grows. -/
theorem stabilizer_eq_bot_iff_adjoin_simple_eq_top [IsGalois F p.SplittingField]
    (x : p.rootSet p.SplittingField) :
    stabilizer p.Gal x = ⊥ ↔ F⟮(x : p.SplittingField)⟯ = ⊤ := by
  refine ⟨fun h => ?_, fun h => ?_⟩
  · rw [← fixedField_stabilizer x, h]
    exact IntermediateField.fixedField_bot
  · rw [stabilizer_eq_fixingSubgroup_adjoin_simple, h]
    exact IntermediateField.fixingSubgroup_top

/-- **A root fixed by the whole Galois group lies in the base field**, and conversely. The
splitting field being Galois over `F` is what makes the fixed field of the whole group `F`
itself; over an inseparable extension a root outside `F` can be fixed by every automorphism. -/
theorem stabilizer_eq_top_iff_adjoin_simple_eq_bot [IsGalois F p.SplittingField]
    (x : p.rootSet p.SplittingField) :
    stabilizer p.Gal x = ⊤ ↔ F⟮(x : p.SplittingField)⟯ = ⊥ := by
  refine ⟨fun h => ?_, fun h => ?_⟩
  · rw [← fixedField_stabilizer x, h]
    exact IsGalois.fixedField_top
  · rw [stabilizer_eq_fixingSubgroup_adjoin_simple, h]
    exact IntermediateField.fixingSubgroup_bot

/-! ### The roots of an irreducible polynomial in a normal extension -/

section Normal

variable {M : Type*} [Field M] [Algebra F M] [Normal F M]

/-- In a normal extension `M / F`, the roots in `M` of an irreducible polynomial over `F` form one
orbit of `Gal(M/F)`: the orbit of any of them. -/
theorem coe_rootSet_eq_orbit_of_irreducible {q : F[X]} (hq : Irreducible q) {α : M}
    (hα : α ∈ q.rootSet M) : (q.rootSet M : Set M) = orbit (M ≃ₐ[F] M) α := by
  ext β
  constructor
  · intro hβ
    rw [← Normal.minpoly_eq_iff_mem_orbit, ← minpoly.eq_of_irreducible hq (mem_rootSet.mp hβ).2,
      ← minpoly.eq_of_irreducible hq (mem_rootSet.mp hα).2]
  · rintro ⟨τ, rfl⟩
    exact smul_mem_rootSet τ hα

/-- The roots in a normal extension `M / F` of an irreducible polynomial over `F`, as the cosets
of the stabilizer in `Gal(M/F)` of a chosen root. -/
noncomputable def rootSetEquivQuotientStabilizer {q : F[X]} (hq : Irreducible q) {α : M}
    (hα : α ∈ q.rootSet M) : q.rootSet M ≃ (M ≃ₐ[F] M) ⧸ stabilizer (M ≃ₐ[F] M) α :=
  (Equiv.subtypeEquivRight fun β =>
    Set.ext_iff.mp (coe_rootSet_eq_orbit_of_irreducible hq hα) β).trans
    (orbitEquivQuotientStabilizer _ α)

/-- The coset of `ρ` corresponds to the root `ρ • α`. -/
@[simp]
theorem coe_rootSetEquivQuotientStabilizer_symm_mk {q : F[X]} (hq : Irreducible q) {α : M}
    (hα : α ∈ q.rootSet M) (ρ : M ≃ₐ[F] M) :
    (((rootSetEquivQuotientStabilizer hq hα).symm
      (ρ : (M ≃ₐ[F] M) ⧸ stabilizer (M ≃ₐ[F] M) α) : q.rootSet M) : M) = ρ • α :=
  orbitEquivQuotientStabilizer_symm_apply (M ≃ₐ[F] M) α ρ

/-- The root `ρ α` corresponds to the coset of `ρ`. -/
@[simp]
theorem rootSetEquivQuotientStabilizer_mk_apply {q : F[X]} (hq : Irreducible q) {α : M}
    (hα : α ∈ q.rootSet M) (ρ : M ≃ₐ[F] M) (h : ρ α ∈ q.rootSet M) :
    rootSetEquivQuotientStabilizer hq hα ⟨ρ α, h⟩ =
      (ρ : (M ≃ₐ[F] M) ⧸ stabilizer (M ≃ₐ[F] M) α) :=
  (Equiv.eq_symm_apply _).mp
    (Subtype.ext (coe_rootSetEquivQuotientStabilizer_symm_mk hq hα ρ).symm)

/-- The identification of the roots with the cosets of a stabilizer is equivariant. -/
@[simp]
theorem rootSetEquivQuotientStabilizer_smul {q : F[X]} (hq : Irreducible q) {α : M}
    (hα : α ∈ q.rootSet M) (g : M ≃ₐ[F] M) (x : q.rootSet M) :
    rootSetEquivQuotientStabilizer hq hα (g • x) = g • rootSetEquivQuotientStabilizer hq hα x := by
  apply (rootSetEquivQuotientStabilizer hq hα).symm.injective
  rw [Equiv.symm_apply_apply]
  obtain ⟨τ, hτ⟩ := QuotientGroup.mk_surjective (rootSetEquivQuotientStabilizer hq hα x)
  have hx : (x : M) = τ • α := by
    have := congrArg (fun c => ((rootSetEquivQuotientStabilizer hq hα).symm c : M)) hτ
    rw [Equiv.symm_apply_apply] at this
    rw [← this, coe_rootSetEquivQuotientStabilizer_symm_mk]
  rw [← hτ, MulAction.Quotient.smul_mk]
  apply Subtype.ext
  rw [coe_rootSetEquivQuotientStabilizer_symm_mk, rootSet.coe_smul, hx, smul_eq_mul, mul_smul]

end Normal

end TauCeti
