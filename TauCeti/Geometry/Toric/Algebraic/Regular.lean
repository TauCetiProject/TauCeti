/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.Geometry.Toric.Algebraic.Fan
public import TauCeti.Geometry.Toric.Algebraic.Ray.Primitive

/-!
# Regular toric cones and regular fans

A toric cone is *regular*, or smooth, when its primitive ray generators can be completed to a
single integral basis of the lattice. This is the combinatorial condition under which the affine
chart of the cone is a mixed chart `ℂ ^ k × (ℂ ^ *) ^ (n - k)` rather than a singular affine toric
variety, so it is the hypothesis carried by every analytic statement about a toric variety built
from a fan.

Regularity is defined here as the conjunction of `TauCeti.Toric.IsToricCone` with the existence of
an *extending basis*: an integral basis `b` of the lattice together with an injection `r` of the
rays of the cone into the basis indices such that `b (r ρ)` is the primitive generator of the ray
`ρ`. Carrying the toric-cone hypothesis is what stops regularity from holding vacuously: an
irrational or nonsalient cone has no rational rays to constrain, so the basis condition alone would
be satisfied by cones that are not cones of smooth affine toric varieties at all.

Two extending bases of the same cone cannot differ at the ray indices, because a ray of a toric
cone in an integral lattice has only one primitive generator. This pins the block form of the
transition matrix between two extending bases: every ray column is a standard column supported at
the matching ray row, so in the splitting of the indices into ray and nonray indices the matrix is
`[[P, B], [0, C]]` with `P` the permutation matrix comparing the two ray indexings. The analytic
layer consumes exactly this shape: changing the extending basis acts on the boundary coordinates
by a permutation and on the torus coordinates by the complementary unimodular block.

## Main declarations

* `TauCeti.Toric.IsExtendingBasis`: an integral basis whose vectors at the ray indices are the
  primitive ray generators.
* `TauCeti.Toric.IsRegularCone`: a toric cone admitting an extending basis.
* `TauCeti.Toric.isRegularCone_bot`: the zero cone, whose affine chart is the dense torus, is
  regular.
* `TauCeti.Toric.isRegularCone_hull_singleton`: the cone spanned by a primitive lattice vector,
  whose affine chart is the complex line, is regular.
* `TauCeti.Toric.IsRegularCone.of_isFaceOf` and `TauCeti.Toric.IsRegularCone.face`: a face of a
  regular cone is regular. Since the pairwise intersections of the cones of a fan are faces, this
  also makes the overlaps of the affine charts of a regular fan regular.
* `TauCeti.Toric.IsRegularCone.prod`: a product of regular cones is regular for the product lattice
  map.
* `TauCeti.Toric.IsRegularCone.card_toricRay_le_finrank`: a regular cone has at most as many rays
  as the rank of the lattice, which is the count that gives the dimensions of its mixed chart.
* `TauCeti.Toric.IsExtendingBasis.basis_apply_eq`,
  `TauCeti.Toric.IsExtendingBasis.repr_basis_apply` and
  `TauCeti.Toric.IsExtendingBasis.toMatrix_apply`: the block form relating two extending bases.
* `TauCeti.Toric.Fan.IsRegular`: a fan all of whose cones are regular, together with the
  regularity of the fan of a regular cone and of subfans.

## Implementation notes

`TauCeti.Toric.IsRegularCone` extends `TauCeti.Toric.IsToricCone`, so lattice rationality,
salience and finite generation of a regular cone are reached by dot notation through the parent
structure rather than by forwarding lemmas.

The index type of an extending basis is `Fin n` for an unconstrained `n` rather than
`Fin (Module.finrank ℤ N)`. The two are interchangeable, since `Module.finrank_eq_card_basis`
identifies `n` with the rank and `TauCeti.Toric.IsRegularCone.exists_basis_finrank` produces the
second form on demand, but the unconstrained index avoids transporting a basis along an equality
of natural numbers every time one is built.

## References

The mathematics is §1.2 and Proposition 1.2.16 of W. Fulton, *Introduction to Toric Varieties*,
and §§1.2 and 1.3 of D. Cox, J. Little and H. Schenck, *Toric Varieties*, where a regular cone is
called smooth.
-/

public section

namespace TauCeti.Toric

variable {N N' V V' : Type*} [AddCommGroup N] [AddCommGroup N'] [AddCommGroup V]
  [AddCommGroup V'] [Module ℝ V] [Module ℝ V'] {i : N →+ V} {i' : N' →+ V'}
  {σ τ : PointedCone ℝ V}

/-! ### Extending bases -/

/-- An integral basis `b` of `N` *extends the primitive ray generators* of a cone `σ` along an
injection `r` of the rays of `σ` into the basis indices when the basis vector `b (r ρ)` is the
primitive generator of the ray `ρ`. -/
structure IsExtendingBasis (i : N →+ V) {σ : PointedCone ℝ V} {n : ℕ}
    (b : Module.Basis (Fin n) ℤ N) (r : ToricRay σ ↪ Fin n) : Prop where
  /-- The basis vector indexed by a ray is the primitive generator of that ray. -/
  isPrimitiveGenerator_apply : ∀ ρ : ToricRay σ, IsPrimitiveGenerator i ρ (b (r ρ))

/-! ### Regular cones -/

/-- A toric cone is *regular*, or smooth, when some integral basis of the lattice extends its
primitive ray generators. The toric-cone hypothesis is part of the definition: without it the
basis condition would hold vacuously for irrational and nonsalient cones, which have no rational
rays. -/
-- Interface source: `TauCetiRoadmap/AnalyticToricGeometry/Suggested.lean`.
structure IsRegularCone (i : N →+ V) (σ : PointedCone ℝ V) : Prop extends IsToricCone i σ where
  /-- Some integral basis extends the primitive ray generators of the cone. -/
  exists_basis : ∃ (n : ℕ) (b : Module.Basis (Fin n) ℤ N) (r : ToricRay σ ↪ Fin n),
    IsExtendingBasis i b r

namespace IsRegularCone

/-- The rays of a regular cone can be indexed inside a basis of rank-many indices. -/
theorem exists_basis_finrank (h : IsRegularCone i σ) :
    ∃ (b : Module.Basis (Fin (Module.finrank ℤ N)) ℤ N)
      (r : ToricRay σ ↪ Fin (Module.finrank ℤ N)), IsExtendingBasis i b r := by
  obtain ⟨n, b, r, hb⟩ := h.exists_basis
  have hn : Module.finrank ℤ N = n := by simpa using Module.finrank_eq_card_basis b
  exact hn ▸ ⟨b, r, hb⟩

/-- A regular cone has at most as many rays as the rank of the lattice. For a regular cone of
dimension `k` in a rank-`n` lattice this is the bound `k ≤ n` behind the mixed chart
`ℂ ^ k × (ℂ ^ *) ^ (n - k)`. -/
theorem card_toricRay_le_finrank (h : IsRegularCone i σ) :
    Nat.card (ToricRay σ) ≤ Module.finrank ℤ N := by
  obtain ⟨b, r, -⟩ := h.exists_basis_finrank
  simpa using Nat.card_le_card_of_injective r r.injective

end IsRegularCone

/-! ### The zero cone and the cone of a ray -/

/-- The zero cone is regular. Its affine chart is the dense torus of the lattice, which is
therefore a smooth chart of every toric variety built from a fan. -/
theorem isRegularCone_bot (hi : IsIntegralLattice i) :
    IsRegularCone i (⊥ : PointedCone ℝ V) := by
  have _ := hi.free
  have _ := hi.finite
  exact ⟨isToricCone_bot i, Module.finrank ℤ N, Module.finBasis ℤ N,
    Function.Embedding.ofIsEmpty, ⟨fun ρ ↦ isEmptyElim ρ⟩⟩

/-- The cone spanned by a primitive lattice vector is regular: a primitive vector belongs to an
integral basis, and the cone it spans is its own only ray. The affine chart of this cone is the
complex line, into which the chart of the zero face is the inclusion of the punctured line. -/
theorem isRegularCone_hull_singleton (hi : IsIntegralLattice i) {v : N} (hv : IsPrimitive v) :
    IsRegularCone i (PointedCone.hull ℝ {i v}) := by
  have _ := hi.free
  have _ := hi.finite
  obtain ⟨n, b, j, hbj⟩ := hv.exists_basis
  have hiv : i v ≠ 0 := fun h ↦ hv.ne_zero (hi.injective (by simpa using h))
  have hinj : Function.Injective fun _ : ToricRay (PointedCone.hull ℝ {i v}) ↦ j :=
    fun ρ ρ' _ ↦ by rw [ToricRay.eq_hullSingleton hiv ρ, ToricRay.eq_hullSingleton hiv ρ']
  refine ⟨isToricCone_hull_singleton i v, n, b, ⟨_, hinj⟩, ⟨fun ρ ↦ ?_⟩⟩
  have hmem : i v ∈ ρ :=
    ρ.toPointedCone_eq_of_hull_singleton.ge (PointedCone.subset_hull (Set.mem_singleton (i v)))
  simp only [Function.Embedding.coeFn_mk, hbj]
  exact isPrimitiveGenerator_iff.2 ⟨hmem, hv⟩

/-! ### Faces -/

namespace IsRegularCone

/-- A face of a regular cone is regular: its rays are rays of the ambient cone, with the same
primitive generators, so an extending basis of the ambient cone restricts to one of the face. -/
theorem of_isFaceOf (hσ : IsRegularCone i σ) (hτ : τ.IsFaceOf σ) : IsRegularCone i τ := by
  obtain ⟨n, b, r, hb⟩ := hσ.exists_basis
  refine ⟨hσ.toIsToricCone.of_isFaceOf hτ, n, b, (ToricRay.faceEmbedding hτ).trans r,
    ⟨fun ρ ↦ ?_⟩⟩
  exact (isPrimitiveGenerator_faceEmbedding hτ ρ).1 (hb.isPrimitiveGenerator_apply _)

/-- Every element of Mathlib's face lattice of a regular cone is a regular cone. Since the
pairwise intersection of two cones of a fan is a face of each of them, the overlaps of the affine
charts of a regular fan are again charts of regular cones. -/
theorem face (hσ : IsRegularCone i σ) (F : σ.Face) : IsRegularCone i F.toPointedCone :=
  hσ.of_isFaceOf F.isFaceOf

end IsRegularCone

/-! ### Products -/

/-- A product of regular cones is regular for the product lattice map. Every ray of the product is
a ray of one of the two factors, so the product of two extending bases extends the primitive ray
generators of the product cone. -/
theorem IsRegularCone.prod {τ' : PointedCone ℝ V'} (hσ : IsRegularCone i σ)
    (hτ' : IsRegularCone i' τ') : IsRegularCone (i.prodMap i') (σ.prod τ') := by
  obtain ⟨n, b, r, hb⟩ := hσ.exists_basis
  obtain ⟨n', b', r', hb'⟩ := hτ'.exists_basis
  have hστ : ((σ.prod τ' : PointedCone ℝ (V × V')) : ConvexCone ℝ (V × V')).Salient :=
    hσ.salient.prod hτ'.salient
  set B := (b.prod b').reindex finSumFinEquiv with hB
  have hBinl : ∀ k : Fin n, B (finSumFinEquiv (Sum.inl k)) = (b k, 0) := fun k ↦ by
    rw [hB, Module.Basis.reindex_apply, Equiv.symm_apply_apply]; simp
  have hBinr : ∀ k : Fin n', B (finSumFinEquiv (Sum.inr k)) = (0, b' k) := fun k ↦ by
    rw [hB, Module.Basis.reindex_apply, Equiv.symm_apply_apply]; simp
  refine ⟨hσ.toIsToricCone.prod hτ'.toIsToricCone, n + n', B,
    (ToricRay.prodSplit hστ).trans ((r.sumMap r').trans finSumFinEquiv.toEmbedding),
    ⟨fun G ↦ ?_⟩⟩
  by_cases hG : PointedCone.map (LinearMap.snd ℝ V V') G.toPointedCone = ⊥
  · set ρ := ToricRay.prodRayFst hστ G hG with hρ
    have hidx : ((ToricRay.prodSplit hστ).trans
        ((r.sumMap r').trans finSumFinEquiv.toEmbedding)) G
        = finSumFinEquiv (Sum.inl (r ρ)) := by
      simp [ToricRay.prodSplit_eq_inl hστ G hG, hρ]
    have hprim : IsPrimitive ((b (r ρ), (0 : N')) : N × N') := by
      have h := B.isPrimitive (finSumFinEquiv (Sum.inl (r ρ)))
      rwa [hBinl] at h
    rw [hidx, hBinl]
    refine isPrimitiveGenerator_iff.2 ⟨G.1.isFaceOf.eq_prod_map.ge
      (Submodule.mem_prod.2 ⟨?_, ?_⟩), hprim⟩
    · exact (isPrimitiveGenerator_iff.1 (hb.isPrimitiveGenerator_apply ρ)).1
    · simp
  · set ρ := ToricRay.prodRaySnd hστ G hG with hρ
    have hidx : ((ToricRay.prodSplit hστ).trans
        ((r.sumMap r').trans finSumFinEquiv.toEmbedding)) G
        = finSumFinEquiv (Sum.inr (r' ρ)) := by
      simp [ToricRay.prodSplit_eq_inr hστ G hG, hρ]
    have hprim : IsPrimitive (((0 : N), b' (r' ρ)) : N × N') := by
      have h := B.isPrimitive (finSumFinEquiv (Sum.inr (r' ρ)))
      rwa [hBinr] at h
    rw [hidx, hBinr]
    refine isPrimitiveGenerator_iff.2 ⟨G.1.isFaceOf.eq_prod_map.ge
      (Submodule.mem_prod.2 ⟨?_, ?_⟩), hprim⟩
    · simp
    · exact (isPrimitiveGenerator_iff.1 (hb'.isPrimitiveGenerator_apply ρ)).1

/-! ### Two extending bases -/

namespace IsExtendingBasis

variable {n n' : ℕ} {b : Module.Basis (Fin n) ℤ N} {b' : Module.Basis (Fin n') ℤ N}
  {r : ToricRay σ ↪ Fin n} {r' : ToricRay σ ↪ Fin n'}

/-- Two integral bases extending the primitive ray generators of a toric cone carry the same
vector at the indices of a given ray: both are primitive generators of that ray, and a ray of a
toric cone in an integral lattice has only one. -/
theorem basis_apply_eq (hi : IsIntegralLattice i) (hσ : IsToricCone i σ)
    (hb : IsExtendingBasis i b r) (hb' : IsExtendingBasis i b' r') (ρ : ToricRay σ) :
    b (r ρ) = b' (r' ρ) :=
  (hb.isPrimitiveGenerator_apply ρ).unique hi hσ (hb'.isPrimitiveGenerator_apply ρ)

/-- The ray columns of the transition matrix between two extending bases are standard columns. -/
theorem repr_basis_apply (hi : IsIntegralLattice i) (hσ : IsToricCone i σ)
    (hb : IsExtendingBasis i b r) (hb' : IsExtendingBasis i b' r') (ρ : ToricRay σ) :
    b'.repr (b (r ρ)) = Finsupp.single (r' ρ) 1 := by
  rw [hb.basis_apply_eq hi hσ hb' ρ, Module.Basis.repr_self]

/-- The block form of the transition matrix between two extending bases. Splitting both index sets
into ray and nonray indices, the matrix reads `[[P, B], [0, C]]`: the column of a ray index carries
a single `1`, in the row of the matching ray index, so the ray block `P` is the permutation matrix
comparing the two ray indexings and the nonray-row, ray-column block vanishes. -/
theorem toMatrix_apply (hi : IsIntegralLattice i) (hσ : IsToricCone i σ)
    (hb : IsExtendingBasis i b r) (hb' : IsExtendingBasis i b' r') (ρ : ToricRay σ)
    (j : Fin n') : b'.toMatrix b j (r ρ) = if j = r' ρ then 1 else 0 := by
  rw [Module.Basis.toMatrix_apply, hb.repr_basis_apply hi hσ hb' ρ, Finsupp.single_apply]
  exact if_congr eq_comm rfl rfl

/-- The ray block of the transition matrix between two extending bases is a permutation matrix. -/
theorem toMatrix_apply_self (hi : IsIntegralLattice i) (hσ : IsToricCone i σ)
    (hb : IsExtendingBasis i b r) (hb' : IsExtendingBasis i b' r') (ρ : ToricRay σ) :
    b'.toMatrix b (r' ρ) (r ρ) = 1 := by
  simp [hb.toMatrix_apply hi hσ hb' ρ]

/-- The nonray-row, ray-column block of the transition matrix between two extending bases
vanishes. -/
theorem toMatrix_apply_eq_zero (hi : IsIntegralLattice i) (hσ : IsToricCone i σ)
    (hb : IsExtendingBasis i b r) (hb' : IsExtendingBasis i b' r') (ρ : ToricRay σ)
    {j : Fin n'} (hj : j ≠ r' ρ) : b'.toMatrix b j (r ρ) = 0 := by
  simp [hb.toMatrix_apply hi hσ hb' ρ, hj]

end IsExtendingBasis

/-! ### Regular fans -/

namespace Fan

/-- A fan is *regular*, or smooth, when every one of its cones is regular. This is the hypothesis
under which the analytic realization of the fan is a complex manifold. -/
-- Interface source: `TauCetiRoadmap/AnalyticToricGeometry/Suggested.lean`.
def IsRegular (Φ : Fan i) : Prop := ∀ ⦃σ⦄, σ ∈ Φ.cones → IsRegularCone i σ

/-- The characteristic property of a regular fan. -/
@[simp]
theorem isRegular_iff {Φ : Fan i} :
    Φ.IsRegular ↔ ∀ σ ∈ Φ.cones, IsRegularCone i σ := Iff.rfl

/-- The fan of a regular cone is regular: its cones are the faces of that cone. -/
theorem isRegular_ofCone (hi : IsIntegralLattice i) (hσ : IsRegularCone i σ) :
    (ofCone hi hσ.toIsToricCone).IsRegular :=
  fun _ hτ ↦ hσ.of_isFaceOf ((mem_ofCone_cones hi hσ.toIsToricCone).1 hτ)

/-- A subfan of a regular fan is regular. -/
theorem IsRegular.subfan {Φ : Fan i} (hΦ : Φ.IsRegular) (S : Set (PointedCone ℝ V))
    (hS : S ⊆ Φ.cones) (hface : ∀ ⦃σ τ⦄, σ ∈ S → τ.IsFaceOf σ → τ ∈ S) :
    (Φ.subfan S hS hface).IsRegular := fun _ hσ ↦ hΦ (hS (by rwa [Φ.subfan_cones] at hσ))

/-- A nonempty regular fan contains the zero cone, whose affine chart is the dense torus. -/
theorem IsRegular.isRegularCone_bot {Φ : Fan i} (hΦ : Φ.IsRegular) (hσ : σ ∈ Φ.cones) :
    IsRegularCone i (⊥ : PointedCone ℝ V) := hΦ (Φ.bot_mem hσ)

end Fan

end TauCeti.Toric
