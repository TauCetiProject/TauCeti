/-
Copyright (c) 2026 Mei contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Claude Code
-/
module

public import TauCeti.Analysis.Convex.Polyhedron.Rational.Basic
public import TauCeti.LinearAlgebra.Alternating.Conormal
public import Mathlib.Analysis.Convex.Intrinsic
public import Mathlib.LinearAlgebra.Finsupp.LSum
public import Mathlib.LinearAlgebra.Quotient.Basic

/-!
# Polyhedral cochains

A polyhedral cochain of codimension `k` with coefficients in `E` is a finite sum of generators
`(P, o, c)`. Here `P` is a nonempty closed rational-normal affine polyhedron of codimension `k`,
`o` is an orientation of the normal quotient `V ⧸ dir P`, and `c ∈ E`. The generators are taken
modulo additivity in `c`, reversal of `o` together with negation of `c`, and subdivision of `P`
into polyhedra of the same codimension carrying the same orientation.

The orientation is recorded on the conormal side, as a ray of alternating `k`-forms on `V`
vanishing as soon as one argument lies in `dir P` (`Module.Ray.IsConormal`). Positive rescaling
of a representing form does not change the generator, and the orientations of all pieces of a
subdivision are literally equal, since the pieces have the direction of the subdivided
polyhedron.

The cochains form an `R`-module for every `R`-module of coefficients, and `R`-linear coefficient
maps act functorially. Taking `R = ℤ` gives cochains with coefficients in an abelian group, and
the `R`-module carrier has the same underlying group as the abelian-group carrier. The quotient
is characterized by its universal property `PolyhedralCochain.lift`. In top codimension every
cell is a point, and a generator with nonzero coefficient is a nonzero cochain.

## Attribution

Adapted from `Mei/Geometry/Convex/PolyhedralCochain/Basic.lean` in
[Mei](https://github.com/yuma-mizuno-lean/Mei) at commit
`3d2e9c869ee44c41ae9c7b5c6e2042898430d0ca` (Apache 2.0). Original copyright and author credit are
retained. The affine-span and relation-containment lemmas follow the same basic module at
commit `a79c57178cc83666fc244ca6e6eeaa722e9b8bc7` (Apache 2.0).
-/

public section

open Module

noncomputable section

namespace TauCeti

variable {N V : Type*} [AddCommGroup N] [NormedAddCommGroup V] [NormedSpace ℝ V]
  {i : N →+ V}

/-- An oriented cell of codimension `k`: a nonempty closed rational-normal affine polyhedron of
codimension `k`, with an orientation of its normal quotient recorded as a ray of alternating
`k`-forms on `V` conormal to the direction of the polyhedron. These are the generators of
polyhedral cochains. -/
@[ext]
structure OrientedCell (h : TauCeti.Toric.IsIntegralLattice i) (k : ℕ) where
  /-- The supporting polyhedron. -/
  carrier : Set V
  /-- The support has a finite rational-normal presentation; in particular it is closed. -/
  rational : IsRationalNormalPolyhedron h carrier
  /-- The support is nonempty. -/
  nonempty : carrier.Nonempty
  /-- The support has codimension `k`. -/
  finrank_direction_add : finrank ℝ (affineSpan ℝ carrier).direction + k = finrank ℝ V
  /-- The orientation of the normal quotient, as a ray of `k`-forms. -/
  orientation : Module.Ray ℝ (V [⋀^Fin k]→ₗ[ℝ] ℝ)
  /-- The orientation is represented by forms conormal to the direction of the support. -/
  isConormal : orientation.IsConormal (affineSpan ℝ carrier).direction

namespace OrientedCell

variable {h : TauCeti.Toric.IsIntegralLattice i} {k : ℕ}

/-- Containment between cells of the same codimension forces their tangent
spaces to agree. -/
theorem direction_eq_of_subset (σ τ : OrientedCell h k) (hστ : σ.carrier ⊆ τ.carrier) :
    (affineSpan ℝ σ.carrier).direction = (affineSpan ℝ τ.carrier).direction := by
  have := h.finiteDimensional
  apply Submodule.eq_of_le_of_finrank_eq
    (AffineSubspace.direction_le (affineSpan_mono ℝ hστ))
  have hσ := σ.finrank_direction_add
  have hτ := τ.finrank_direction_add
  omega

/-- The degree of a cell's conormal orientation is the dimension of its normal quotient. -/
theorem finrank_quotient_direction (σ : OrientedCell h k) :
    finrank ℝ (V ⧸ (affineSpan ℝ σ.carrier).direction) = k := by
  have := h.finiteDimensional
  have := (affineSpan ℝ σ.carrier).direction.finrank_quotient_add_finrank
  have := σ.finrank_direction_add
  omega

/-- The same polyhedron with the opposite orientation. -/
def reverse (σ : OrientedCell h k) : OrientedCell h k where
  carrier := σ.carrier
  rational := σ.rational
  nonempty := σ.nonempty
  finrank_direction_add := σ.finrank_direction_add
  orientation := -σ.orientation
  isConormal := Module.Ray.isConormal_neg_iff.mpr σ.isConormal

@[simp]
theorem reverse_carrier (σ : OrientedCell h k) : σ.reverse.carrier = σ.carrier := (rfl)

@[simp]
theorem reverse_orientation (σ : OrientedCell h k) :
    σ.reverse.orientation = -σ.orientation := (rfl)

@[simp]
theorem reverse_reverse (σ : OrientedCell h k) : σ.reverse.reverse = σ := by
  ext1
  · rfl
  · exact neg_neg σ.orientation

/-- Reversal changes the cell. -/
theorem reverse_ne_self (σ : OrientedCell h k) : σ.reverse ≠ σ := fun hσ =>
  σ.orientation.ne_neg_self (by rw [← reverse_orientation, hσ])

/-- Two oriented cells with the same support agree up to orientation reversal. -/
theorem eq_or_eq_reverse_of_carrier_eq (σ τ : OrientedCell h k)
    (hc : σ.carrier = τ.carrier) : σ = τ ∨ σ = τ.reverse := by
  have := h.finiteDimensional
  have hτ : τ.orientation.IsConormal (affineSpan ℝ σ.carrier).direction := by
    rw [hc]
    exact τ.isConormal
  rcases σ.isConormal.eq_or_eq_neg hτ
    (by simpa using σ.finrank_quotient_direction) with ho | ho
  · exact Or.inl (OrientedCell.ext hc ho)
  · apply Or.inr
    apply OrientedCell.ext
    · simpa only [reverse_carrier] using hc
    · simpa only [reverse_orientation] using ho

/-- In top codimension the support of a cell is a single point. -/
theorem exists_carrier_eq_singleton (hk : k = finrank ℝ V) (σ : OrientedCell h k) :
    ∃ x, σ.carrier = {x} := by
  have := h.finiteDimensional
  have hdir : (affineSpan ℝ σ.carrier).direction = ⊥ :=
    Submodule.finrank_eq_zero.mp (by have := σ.finrank_direction_add; omega)
  rw [direction_affineSpan, vectorSpan_eq_bot_iff_subsingleton] at hdir
  obtain ⟨x, hx⟩ := σ.nonempty
  exact ⟨x, hdir.eq_singleton_of_mem hx⟩

variable (h) in
/-- The point `x` as a cell of top codimension, with the orientation `o` of `V`. -/
def point (x : V) (o : Orientation ℝ V (Fin (finrank ℝ V))) : OrientedCell h (finrank ℝ V) where
  carrier := {x}
  rational := isRationalNormalPolyhedron_singleton h x
  nonempty := Set.singleton_nonempty x
  finrank_direction_add := by
    rw [direction_affineSpan, vectorSpan_singleton, finrank_bot, zero_add]
  orientation := o
  isConormal := by
    rw [direction_affineSpan, vectorSpan_singleton]
    exact o.isConormal_bot

@[simp]
theorem point_carrier (x : V) (o : Orientation ℝ V (Fin (finrank ℝ V))) :
    (point h x o).carrier = {x} := (rfl)

@[simp]
theorem point_orientation (x : V) (o : Orientation ℝ V (Fin (finrank ℝ V))) :
    (point h x o).orientation = o := (rfl)

/-- `Q` is an oriented subdivision of `σ`: the supports of the cells of `Q` cover the support of
`σ`, have pairwise disjoint relative interiors, and carry the orientation of `σ`. Since each piece
has the codimension of `σ` and lies in its support, it has the direction of `σ`, so this is the
induced orientation. -/
structure IsOrientedSubdivision (σ : OrientedCell h k) (Q : Finset (OrientedCell h k)) :
    Prop where
  /-- The pieces cover the subdivided support. -/
  biUnion_carrier : ⋃ τ ∈ Q, τ.carrier = σ.carrier
  /-- Distinct pieces have disjoint relative interiors. -/
  pairwiseDisjoint :
    (Q : Set (OrientedCell h k)).PairwiseDisjoint fun τ => intrinsicInterior ℝ τ.carrier
  /-- Every piece carries the orientation of the subdivided cell. -/
  orientation_eq : ∀ τ ∈ Q, τ.orientation = σ.orientation

namespace IsOrientedSubdivision

variable {σ τ : OrientedCell h k} {Q : Finset (OrientedCell h k)}

/-- Every piece lies in the subdivided support. -/
theorem carrier_subset (hQ : IsOrientedSubdivision σ Q) (hτ : τ ∈ Q) :
    τ.carrier ⊆ σ.carrier := by
  rw [← hQ.biUnion_carrier]
  exact Set.subset_biUnion_of_mem (u := fun τ : OrientedCell h k => τ.carrier) hτ

/-- Every piece has the direction of the subdivided cell, since it lies in the subdivided support
and has the same codimension. -/
theorem direction_eq (hQ : IsOrientedSubdivision σ Q) (hτ : τ ∈ Q) :
    (affineSpan ℝ τ.carrier).direction = (affineSpan ℝ σ.carrier).direction :=
  τ.direction_eq_of_subset σ (hQ.carrier_subset hτ)

/-- Every piece has the affine span of the subdivided cell. -/
theorem affineSpan_eq (hQ : IsOrientedSubdivision σ Q) (hτ : τ ∈ Q) :
    affineSpan ℝ τ.carrier = affineSpan ℝ σ.carrier := by
  obtain ⟨x, hx⟩ := τ.nonempty
  exact AffineSubspace.ext_of_direction_eq (hQ.direction_eq hτ)
    ⟨x, subset_affineSpan ℝ _ hx, subset_affineSpan ℝ _ (hQ.carrier_subset hτ hx)⟩

/-- A subdivision has at least one piece. -/
theorem nonempty (hQ : IsOrientedSubdivision σ Q) : Q.Nonempty := by
  obtain ⟨x, hx⟩ := σ.nonempty
  rw [← hQ.biUnion_carrier, Set.mem_iUnion₂] at hx
  obtain ⟨τ, hτ, -⟩ := hx
  exact ⟨τ, hτ⟩

end IsOrientedSubdivision

end OrientedCell

/-- A nonempty rational-normal polyhedron of codimension `k` admits a conormal
orientation, hence is the carrier of an oriented cell. -/
theorem IsRationalNormalPolyhedron.exists_orientedCell
    {h : TauCeti.Toric.IsIntegralLattice i} {P : Set V} {k : ℕ}
    (hP : IsRationalNormalPolyhedron h P) (hne : P.Nonempty)
    (hdim : finrank ℝ (affineSpan ℝ P).direction + k = finrank ℝ V) :
    ∃ σ : OrientedCell h k, σ.carrier = P := by
  have := h.finiteDimensional
  let W := (affineSpan ℝ P).direction
  have hk : finrank ℝ (V ⧸ W) = k := by
    have hdimW : finrank ℝ W + k = finrank ℝ V := hdim
    have := W.finrank_quotient_add_finrank
    omega
  let b := Module.finBasisOfFinrankEq ℝ (V ⧸ W) hk
  have hα : b.det.compLinearMap W.mkQ ≠ 0 := by
    intro hz
    apply b.det_ne_zero
    exact AlternatingMap.compLinearMap_injective W.mkQ W.mkQ_surjective
      (by simpa only [AlternatingMap.zero_compLinearMap] using hz)
  refine ⟨⟨P, hP, hne, hdim, rayOfNeZero ℝ _ hα, ?_⟩, rfl⟩
  rw [Module.Ray.isConormal_rayOfNeZero_iff]
  simpa only [Submodule.conormalFormsEquiv_apply] using
    (W.conormalFormsEquiv b.det).property

open OrientedCell

variable (R : Type*) [Ring R] (h : TauCeti.Toric.IsIntegralLattice i)
  (E : Type*) [AddCommGroup E] [Module R E] (k : ℕ)

/-- The relators of polyhedral cochains: reversal `(σ.reverse, c) + (σ, c)` and
subdivision `(σ, c) - ∑ τ ∈ Q, (τ, c)`. Additivity in the coefficient holds already in the
finitely supported functions. The set of relators does not depend on a ring of scalars. -/
def cochainRelators : Set (OrientedCell h k →₀ E) :=
  {x | ∃ (σ : OrientedCell h k) (c : E), x = Finsupp.single σ.reverse c + Finsupp.single σ c} ∪
    {x | ∃ (σ : OrientedCell h k) (Q : Finset (OrientedCell h k)) (c : E),
      IsOrientedSubdivision σ Q ∧ x = Finsupp.single σ c - ∑ τ ∈ Q, Finsupp.single τ c}

/-- Membership in `cochainRelators`: a reversal or a subdivision relator. -/
theorem mem_cochainRelators_iff {x : OrientedCell h k →₀ E} :
    x ∈ cochainRelators h E k ↔
      (∃ (σ : OrientedCell h k) (c : E), x = Finsupp.single σ.reverse c + Finsupp.single σ c) ∨
        ∃ (σ : OrientedCell h k) (Q : Finset (OrientedCell h k)) (c : E),
          IsOrientedSubdivision σ Q ∧ x = Finsupp.single σ c - ∑ τ ∈ Q, Finsupp.single τ c :=
  Iff.rfl

/-- The `R`-submodule of relations spanned by `cochainRelators`. -/
def cochainRelations : Submodule R (OrientedCell h k →₀ E) :=
  Submodule.span R (cochainRelators h E k)

/-- The relations are the span of the relators. -/
theorem cochainRelations_def :
    cochainRelations R h E k = Submodule.span R (cochainRelators h E k) := (rfl)

variable {R h E k} in
/-- A submodule contains all cochain relations exactly when it contains the reversal relations
and the subdivision relations. -/
theorem cochainRelations_le_iff {p : Submodule R (OrientedCell h k →₀ E)} :
    cochainRelations R h E k ≤ p ↔
      (∀ (σ : OrientedCell h k) (c : E), Finsupp.single σ.reverse c + Finsupp.single σ c ∈ p) ∧
        ∀ (σ : OrientedCell h k) (Q : Finset (OrientedCell h k)) (c : E),
          IsOrientedSubdivision σ Q → Finsupp.single σ c - ∑ τ ∈ Q, Finsupp.single τ c ∈ p := by
  rw [cochainRelations, Submodule.span_le]
  constructor
  · intro hp
    exact ⟨fun σ c => hp (Or.inl ⟨σ, c, rfl⟩), fun σ Q c hQ => hp (Or.inr ⟨σ, Q, c, hQ, rfl⟩)⟩
  · rintro ⟨hrev, hsub⟩ x (⟨σ, c, rfl⟩ | ⟨σ, Q, c, hQ, rfl⟩)
    exacts [hrev σ c, hsub σ Q c hQ]

/-- Polyhedral cochains of codimension `k` with coefficients in the `R`-module `E`: finite sums
of oriented cells with coefficients in `E`, modulo reversal and subdivision. -/
def PolyhedralCochain : Type _ :=
  (OrientedCell h k →₀ E) ⧸ cochainRelations R h E k

namespace PolyhedralCochain

instance : AddCommGroup (PolyhedralCochain R h E k) :=
  inferInstanceAs (AddCommGroup ((OrientedCell h k →₀ E) ⧸ cochainRelations R h E k))

instance : Module R (PolyhedralCochain R h E k) :=
  inferInstanceAs (Module R ((OrientedCell h k →₀ E) ⧸ cochainRelations R h E k))

variable {R h E k}

/-- The cochain represented by a finite formal sum of generators. -/
def ofFinsupp : (OrientedCell h k →₀ E) →ₗ[R] PolyhedralCochain R h E k :=
  (cochainRelations R h E k).mkQ

/-- Every cochain is represented by a finite formal sum of generators. -/
theorem ofFinsupp_surjective :
    Function.Surjective (ofFinsupp : (OrientedCell h k →₀ E) →ₗ[R] PolyhedralCochain R h E k) :=
  (cochainRelations R h E k).mkQ_surjective

/-- The formal sums representing zero are exactly the relations. -/
@[simp]
theorem ker_ofFinsupp :
    LinearMap.ker (ofFinsupp : (OrientedCell h k →₀ E) →ₗ[R] PolyhedralCochain R h E k) =
      cochainRelations R h E k :=
  (cochainRelations R h E k).ker_mkQ

/-- A formal sum represents zero exactly when it is a relation. -/
theorem ofFinsupp_eq_zero_iff {x : OrientedCell h k →₀ E} :
    ofFinsupp (R := R) x = 0 ↔ x ∈ cochainRelations R h E k := by
  rw [← LinearMap.mem_ker, ker_ofFinsupp]

/-- The cochain represented by the generator `(σ, c)`, as a linear map in the coefficient `c`. -/
def mk (σ : OrientedCell h k) : E →ₗ[R] PolyhedralCochain R h E k :=
  ofFinsupp ∘ₗ Finsupp.lsingle σ

@[simp]
theorem ofFinsupp_single (σ : OrientedCell h k) (c : E) :
    ofFinsupp (R := R) (Finsupp.single σ c) = mk σ c := (rfl)

/-- Reversing the orientation of a generator negates its class. -/
@[simp]
theorem mk_reverse (σ : OrientedCell h k) (c : E) :
    mk (R := R) σ.reverse c = -mk σ c := by
  rw [eq_neg_iff_add_eq_zero, ← ofFinsupp_single, ← ofFinsupp_single, ← map_add,
    ofFinsupp_eq_zero_iff, cochainRelations_def]
  exact Submodule.subset_span (Or.inl ⟨σ, c, rfl⟩)

/-- The class of a generator is the sum of the classes of the pieces of an oriented subdivision. -/
theorem mk_eq_sum_of_isOrientedSubdivision {σ : OrientedCell h k}
    {Q : Finset (OrientedCell h k)} (hQ : IsOrientedSubdivision σ Q) (c : E) :
    mk (R := R) σ c = ∑ τ ∈ Q, mk τ c := by
  rw [← sub_eq_zero]
  simp only [← ofFinsupp_single, ← map_sum, ← map_sub, ofFinsupp_eq_zero_iff, cochainRelations_def]
  exact Submodule.subset_span (Or.inr ⟨σ, Q, c, hQ, rfl⟩)

/-- Every cochain is built from generator classes by addition. -/
@[elab_as_elim]
theorem induction_on {p : PolyhedralCochain R h E k → Prop} (x : PolyhedralCochain R h E k)
    (zero : p 0) (add : ∀ x y, p x → p y → p (x + y))
    (mk : ∀ (σ : OrientedCell h k) (c : E), p (mk σ c)) : p x := by
  obtain ⟨x, rfl⟩ := ofFinsupp_surjective x
  induction x using Finsupp.induction_linear with
  | zero => rwa [map_zero]
  | add f g hf hg => rw [map_add]; exact add _ _ hf hg
  | single σ c => rw [ofFinsupp_single]; exact mk σ c

variable {M : Type*} [AddCommGroup M] [Module R M]

/-- Linear maps out of cochains are determined by their values on generators. -/
@[ext]
theorem hom_ext {f g : PolyhedralCochain R h E k →ₗ[R] M}
    (H : ∀ σ : OrientedCell h k, f ∘ₗ mk σ = g ∘ₗ mk σ) : f = g :=
  Submodule.linearMap_qext _ (Finsupp.lhom_ext' H)

/-- The universal property of cochains: a family of linear maps on coefficients, changing sign
under reversal and additive under oriented subdivision, descends to cochains. -/
def lift (φ : OrientedCell h k → E →ₗ[R] M) (reverse : ∀ σ, φ σ.reverse = -φ σ)
    (subdivision : ∀ σ Q, IsOrientedSubdivision σ Q → φ σ = ∑ τ ∈ Q, φ τ) :
    PolyhedralCochain R h E k →ₗ[R] M :=
  (cochainRelations R h E k).liftQ (Finsupp.lsum ℕ φ) <| by
    rw [cochainRelations_def, Submodule.span_le]
    rintro x (⟨σ, c, rfl⟩ | ⟨σ, Q, c, hQ, rfl⟩)
    · rw [SetLike.mem_coe, LinearMap.mem_ker, map_add]
      simp [reverse]
    · rw [SetLike.mem_coe, LinearMap.mem_ker, map_sub, map_sum]
      simp [subdivision σ Q hQ, LinearMap.sum_apply]

variable (φ : OrientedCell h k → E →ₗ[R] M) (reverse : ∀ σ, φ σ.reverse = -φ σ)
  (subdivision : ∀ σ Q, IsOrientedSubdivision σ Q → φ σ = ∑ τ ∈ Q, φ τ)

@[simp]
theorem lift_mk (σ : OrientedCell h k) (c : E) :
    lift φ reverse subdivision (mk σ c) = φ σ c :=
  Finsupp.lsum_single (S := ℕ) φ σ c

@[simp]
theorem lift_comp_mk (σ : OrientedCell h k) : lift φ reverse subdivision ∘ₗ mk σ = φ σ := by
  ext c
  exact lift_mk φ reverse subdivision σ c

/-- `lift` is the unique linear map with the prescribed values on generators. -/
theorem lift_unique (f : PolyhedralCochain R h E k →ₗ[R] M) (hf : ∀ σ, f ∘ₗ mk σ = φ σ) :
    f = lift φ reverse subdivision :=
  hom_ext fun σ => by rw [hf, lift_comp_mk]

section map

variable {E' E'' : Type*} [AddCommGroup E'] [Module R E'] [AddCommGroup E''] [Module R E'']

/-- A linear map of coefficients acts on cochains generator by generator. For coefficients in
abelian groups, take `R = ℤ` and the `ℤ`-linear map underlying an additive map. -/
def map (f : E →ₗ[R] E') : PolyhedralCochain R h E k →ₗ[R] PolyhedralCochain R h E' k :=
  lift (fun σ => mk σ ∘ₗ f)
    (fun σ => by ext c; simp)
    (fun σ Q hQ => by ext c; simp [mk_eq_sum_of_isOrientedSubdivision hQ])

@[simp]
theorem map_mk (f : E →ₗ[R] E') (σ : OrientedCell h k) (c : E) :
    map f (mk σ c) = mk σ (f c) :=
  lift_mk _ _ _ σ c

/-- Changing coefficients in a finite presentation represents the induced map
of its cochain class. -/
@[simp]
theorem map_ofFinsupp (f : E →ₗ[R] E') (x : OrientedCell h k →₀ E) :
    map f (ofFinsupp (R := R) x) = ofFinsupp (Finsupp.mapRange.linearMap f x) := by
  induction x using Finsupp.induction_linear with
  | zero => simp
  | add x y hx hy => simp only [map_add, hx, hy]
  | single σ c => simp

@[simp]
theorem map_id : map (h := h) (k := k) (LinearMap.id : E →ₗ[R] E) = LinearMap.id := by
  ext σ c
  simp

theorem map_comp (g : E' →ₗ[R] E'') (f : E →ₗ[R] E') :
    map (h := h) (k := k) (g ∘ₗ f) = map g ∘ₗ map f := by
  ext σ c
  simp

end map

section restrictScalars

private theorem smul_mem_span_cochainRelators (r : R) {x : OrientedCell h k →₀ E}
    (hx : x ∈ Submodule.span ℤ (cochainRelators h E k)) :
    r • x ∈ Submodule.span ℤ (cochainRelators h E k) := by
  induction hx using Submodule.span_induction with
  | mem x hx =>
    apply Submodule.subset_span
    rcases hx with ⟨σ, c, rfl⟩ | ⟨σ, Q, c, hQ, rfl⟩
    · exact Or.inl ⟨σ, r • c, by simp [smul_add]⟩
    · exact Or.inr ⟨σ, Q, r • c, hQ, by simp [smul_sub, Finset.smul_sum]⟩
  | zero => simp
  | add x y _ _ hx hy => simpa [smul_add] using add_mem hx hy
  | smul n x _ hx => simpa [smul_comm r n x] using Submodule.smul_mem _ n hx

variable (R h E k) in
/-- The relations do not depend on the ring of scalars: as additive subgroups, the `R`-relations
are the `ℤ`-relations. -/
theorem restrictScalars_cochainRelations :
    (cochainRelations R h E k).restrictScalars ℤ = cochainRelations ℤ h E k := by
  refine le_antisymm ?_ (Submodule.span_le_restrictScalars ℤ R _)
  let P : Submodule R (OrientedCell h k →₀ E) :=
    { (cochainRelations ℤ h E k).toAddSubmonoid with
      smul_mem' := fun r _ hx => smul_mem_span_cochainRelators r hx }
  exact Submodule.restrictScalars_mono ℤ
    (Submodule.span_le (p := P) |>.mpr Submodule.subset_span)

variable (R h E k) in
/-- The `R`-module of cochains has the underlying group of the cochains with coefficients in the
abelian group `E`. -/
def restrictScalarsEquiv : PolyhedralCochain ℤ h E k ≃+ PolyhedralCochain R h E k :=
  ((Submodule.quotEquivOfEq _ _ (restrictScalars_cochainRelations R h E k).symm).trans
    (Submodule.Quotient.restrictScalarsEquiv ℤ (cochainRelations R h E k))).toAddEquiv

@[simp]
theorem restrictScalarsEquiv_mk (σ : OrientedCell h k) (c : E) :
    restrictScalarsEquiv R h E k (mk σ c) = mk σ c := by
  -- `PolyhedralCochain` is not exposed, so the quotient API only applies after `change`
  -- re-reads both sides as classes in the quotient `(OrientedCell h k →₀ E) ⧸ _`.
  change Submodule.Quotient.restrictScalarsEquiv ℤ (cochainRelations R h E k)
      (Submodule.quotEquivOfEq _ _ (restrictScalars_cochainRelations R h E k).symm
        (Submodule.Quotient.mk (Finsupp.single σ c))) = Submodule.Quotient.mk (Finsupp.single σ c)
  rw [Submodule.quotEquivOfEq_mk, Submodule.Quotient.restrictScalarsEquiv_mk]

end restrictScalars

section top

open Classical in
/-- The coefficient of a top-codimensional cell at the point `x`, relative to the orientation
`o`. -/
private def pointValue (x : V) (o : Module.Ray ℝ (V [⋀^Fin k]→ₗ[ℝ] ℝ)) (τ : OrientedCell h k) :
    E →ₗ[R] E :=
  if τ.carrier = {x} then (if τ.orientation = o then LinearMap.id else -LinearMap.id) else 0

private theorem pointValue_reverse (hk : k = finrank ℝ V) (x : V)
    (o : Module.Ray ℝ (V [⋀^Fin k]→ₗ[ℝ] ℝ)) (τ : OrientedCell h k) :
    pointValue (R := R) (E := E) x o τ.reverse = -pointValue x o τ := by
  have := h.finiteDimensional
  unfold pointValue
  rw [reverse_carrier, reverse_orientation]
  split_ifs with hx h₁ h₂ h₂
  · exact (o.ne_neg_self (h₂ ▸ h₁).symm).elim
  · rw [neg_neg]
  · rfl
  · have hτo := (Orientation.eq_or_eq_neg τ.orientation o (by simp [hk])).resolve_left h₂
    exact (h₁ ((congrArg Neg.neg hτo).trans (neg_neg o))).elim
  · rw [neg_zero]

private theorem pointValue_subdivision (hk : k = finrank ℝ V) (x : V)
    (o : Module.Ray ℝ (V [⋀^Fin k]→ₗ[ℝ] ℝ)) {σ : OrientedCell h k}
    {Q : Finset (OrientedCell h k)} (hQ : IsOrientedSubdivision σ Q) :
    pointValue (R := R) (E := E) x o σ = ∑ τ ∈ Q, pointValue x o τ := by
  by_cases hσ : σ.carrier = {x}
  · -- Every piece of a subdivided point is the point with the same orientation.
    have hτσ : ∀ τ ∈ Q, τ = σ := fun τ hτ => by
      ext1
      · exact (τ.nonempty.subset_singleton_iff.mp (hσ ▸ hQ.carrier_subset hτ)).trans hσ.symm
      · exact hQ.orientation_eq τ hτ
    obtain ⟨τ, hτ⟩ := hQ.nonempty
    rw [Finset.eq_singleton_iff_unique_mem.mpr ⟨hτσ τ hτ ▸ hτ, hτσ⟩, Finset.sum_singleton]
  · -- No piece is the point `x`, since `σ` is a point different from `x`.
    have hτ : ∀ τ ∈ Q, τ.carrier ≠ {x} := by
      intro τ hτ hτx
      obtain ⟨y, hy⟩ := σ.exists_carrier_eq_singleton hk
      have hxσ : x ∈ σ.carrier := hQ.carrier_subset hτ (by simp [hτx])
      rw [hy, Set.mem_singleton_iff] at hxσ
      exact hσ (hxσ ▸ hy)
    unfold pointValue
    rw [ite_eq_right hσ, eq_comm]
    exact Finset.sum_eq_zero fun τ hτQ => ite_eq_right (hτ τ hτQ)

/-- In top codimension a generator with nonzero coefficient is a nonzero cochain: the
relations identify a point cell only with itself and its reversal. -/
theorem mk_ne_zero_of_finrank_eq (hk : k = finrank ℝ V) (σ : OrientedCell h k) {c : E}
    (hc : c ≠ 0) : mk (R := R) σ c ≠ 0 := by
  obtain ⟨x, hx⟩ := σ.exists_carrier_eq_singleton hk
  intro hzero
  have := congrArg (lift (pointValue x σ.orientation) (pointValue_reverse hk x σ.orientation)
    fun _ _ hQ => pointValue_subdivision hk x σ.orientation hQ) hzero
  simp only [lift_mk, map_zero, pointValue, hx, ite_eq_left, LinearMap.id_apply] at this
  exact hc this

/-- For nonzero coefficients, the top-codimensional cochains form a nontrivial group. -/
instance [Nontrivial E] : Nontrivial (PolyhedralCochain R h E (finrank ℝ V)) := by
  have := h.finiteDimensional
  obtain ⟨c, hc⟩ := exists_ne (0 : E)
  exact ⟨⟨mk (point h 0 (Module.finBasis ℝ V).orientation) c, 0,
    mk_ne_zero_of_finrank_eq rfl _ hc⟩⟩

end top

end PolyhedralCochain

end TauCeti

end
