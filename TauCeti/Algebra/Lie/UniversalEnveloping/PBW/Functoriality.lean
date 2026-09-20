/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.Algebra.Lie.UniversalEnveloping.PBW.AssociatedGraded
public import TauCeti.Algebra.Lie.UniversalEnveloping.Functoriality
public import TauCeti.LinearAlgebra.SymmetricAlgebra.Functoriality

/-!
# Functoriality of the PBW filtration

Every homomorphism of Lie algebras induces a filtered homomorphism of their universal enveloping
algebras: a word of at most `k` canonical generators is sent to a word of at most `k` canonical
generators. Passing to successive quotients gives linear maps on the homogeneous pieces and an
algebra homomorphism of PBW associated gradeds. The canonical map from the symmetric algebra is
natural with respect to these homomorphisms.

The image statements retain information which an inclusion alone would discard. A split
epimorphism maps each filtration step onto the corresponding target step. For a split
monomorphism, the image of a filtration step is exactly the target step intersected with the range
of the enveloping-algebra map. Consequently, an equivalence of Lie algebras identifies the
filtration steps by linear equivalences.

These results do not use the Poincare--Birkhoff--Witt basis theorem. In particular, the exact image
statement for an arbitrary, not necessarily split, Lie subalgebra inclusion remains part of the
ordered-monomial stage of PBW.

## Main definitions and results

* `TauCeti.UniversalEnvelopingAlgebra.map_mem_pbwFiltration` and
  `TauCeti.UniversalEnvelopingAlgebra.map_pbwFiltration_le`: induced maps preserve PBW degree.
* `TauCeti.UniversalEnvelopingAlgebra.mapFiltration`: the induced linear map between filtration
  steps, functorial in the Lie homomorphism.
* `TauCeti.UniversalEnvelopingAlgebra.map_pbwFiltration_eq_of_rightInverse`: split epimorphisms map
  each filtration step onto the corresponding target step.
* `TauCeti.UniversalEnvelopingAlgebra.map_pbwFiltration_eq_inf_range_of_leftInverse`: for a split
  monomorphism, a source step maps to the intersection of the target step with the map's range.
* `TauCeti.UniversalEnvelopingAlgebra.mapEquivFiltration`: a Lie equivalence induces a linear
  equivalence on every filtration step.
* `TauCeti.UniversalEnvelopingAlgebra.mapGradedPiece`: the induced linear map on each successive
  quotient.
* `TauCeti.UniversalEnvelopingAlgebra.mapAssociatedGraded`: the induced algebra homomorphism of
  PBW associated gradeds.
* `TauCeti.UniversalEnvelopingAlgebra.mapAssociatedGraded_comp_pbwAssociatedGradedMap`: the
  canonical map from the symmetric algebra is natural.

-/

public section

open scoped DirectSum

namespace TauCeti.UniversalEnvelopingAlgebra

universe u v w x

variable (R : Type u) [CommRing R]
variable {L : Type v} {M : Type w} {N : Type x}
variable [LieRing L] [LieAlgebra R L]
variable [LieRing M] [LieAlgebra R M]
variable [LieRing N] [LieAlgebra R N]

attribute [local instance 100] LieRing.ofAssociativeRing

/-- The image of a PBW filtration step under an induced enveloping-algebra map lies in the
corresponding target step. -/
theorem map_pbwFiltration_le (f : LieHom R L M) (k : ℕ) :
    (pbwFiltration R L k).map (map R f).toLinearMap ≤ pbwFiltration R M k := by
  rw [pbwFiltration_eq_pow, pbwFiltration_eq_pow]
  simpa only [TauCeti.Algebra.wordFiltration_eq_pow] using
    TauCeti.Algebra.map_wordFiltration_le
      (_root_.UniversalEnvelopingAlgebra.ι R).toLinearMap (map R f)
      (_root_.UniversalEnvelopingAlgebra.ι R).toLinearMap
      (fun x => by
        simpa only [LieHom.coe_toLinearMap, map_ι] using
          TauCeti.Algebra.apply_mem_wordFiltration_one
            (_root_.UniversalEnvelopingAlgebra.ι R :
              M →ₗ⁅R⁆ _root_.UniversalEnvelopingAlgebra R M).toLinearMap (f x)) k

/-- A homomorphism of Lie algebras sends an element of PBW filtration degree at most `k` to one of
degree at most `k`. -/
theorem map_mem_pbwFiltration (f : LieHom R L M) {k : ℕ}
    {x : _root_.UniversalEnvelopingAlgebra R L} (hx : x ∈ pbwFiltration R L k) :
    map R f x ∈ pbwFiltration R M k :=
  map_pbwFiltration_le R f k ⟨x, hx, rfl⟩

/-- Induced enveloping-algebra maps also preserve the step immediately preceding a PBW
filtration degree. -/
theorem map_pbwFiltrationPrevious_le (f : LieHom R L M) (k : ℕ) :
    (pbwFiltrationPrevious R L k).map (map R f).toLinearMap ≤
      pbwFiltrationPrevious R M k := by
  cases k with
  | zero => simp
  | succ k => simpa using map_pbwFiltration_le R f k

/-- A homomorphism of Lie algebras sends an element of the step preceding PBW filtration degree
`k` to one of the corresponding preceding step. -/
theorem map_mem_pbwFiltrationPrevious (f : LieHom R L M) {k : ℕ}
    {x : _root_.UniversalEnvelopingAlgebra R L} (hx : x ∈ pbwFiltrationPrevious R L k) :
    map R f x ∈ pbwFiltrationPrevious R M k :=
  map_pbwFiltrationPrevious_le R f k ⟨x, hx, rfl⟩

/-- The linear map between the `k`-th PBW filtration steps induced by a Lie homomorphism. -/
noncomputable def mapFiltration (f : LieHom R L M) (k : ℕ) :
    pbwFiltration R L k →ₗ[R] pbwFiltration R M k :=
  (map R f).toLinearMap.restrict fun _ hx => map_mem_pbwFiltration R f hx

/-- The map between PBW filtration steps acts by the induced enveloping-algebra map. -/
@[simp]
theorem mapFiltration_apply (f : LieHom R L M) (k : ℕ) (x : pbwFiltration R L k) :
    mapFiltration R f k x = map R f x :=
  LinearMap.coe_restrict_apply _ _

/-- The identity Lie homomorphism induces the identity on each PBW filtration step. -/
@[simp]
theorem mapFiltration_id (k : ℕ) :
    mapFiltration R (LieHom.id : LieHom R L L) k = LinearMap.id := by
  apply LinearMap.ext
  intro x
  apply Subtype.ext
  simp only [mapFiltration_apply, LinearMap.id_apply, map_id, AlgHom.id_apply]

/-- Composition of Lie homomorphisms becomes composition of their maps between PBW filtration
steps. -/
@[simp]
theorem mapFiltration_comp (f : LieHom R L M) (g : LieHom R M N) (k : ℕ) :
    mapFiltration R (g.comp f) k = (mapFiltration R g k).comp (mapFiltration R f k) := by
  apply LinearMap.ext
  intro x
  apply Subtype.ext
  simp only [mapFiltration_apply, LinearMap.comp_apply, map_comp, AlgHom.comp_apply]

/-- A split epimorphism of Lie algebras maps every PBW filtration step onto the corresponding
target step. -/
theorem map_pbwFiltration_eq_of_rightInverse (f : LieHom R L M) (g : LieHom R M L)
    (h : f.comp g = LieHom.id) (k : ℕ) :
    (pbwFiltration R L k).map (map R f).toLinearMap = pbwFiltration R M k := by
  apply le_antisymm (map_pbwFiltration_le R f k)
  intro y hy
  refine ⟨map R g y, map_mem_pbwFiltration R g hy, ?_⟩
  exact map_rightInverse R h y

/-- For a split monomorphism of Lie algebras, the image of the `k`-th PBW filtration step is the
intersection of the target step with the range of the induced enveloping-algebra map. -/
theorem map_pbwFiltration_eq_inf_range_of_leftInverse (f : LieHom R L M) (g : LieHom R M L)
    (h : g.comp f = LieHom.id) (k : ℕ) :
    (pbwFiltration R L k).map (map R f).toLinearMap =
      pbwFiltration R M k ⊓ LinearMap.range (map R f).toLinearMap := by
  have hcomap : pbwFiltration R L k =
      (pbwFiltration R M k).comap (map R f).toLinearMap := by
    apply le_antisymm
    · exact Submodule.map_le_iff_le_comap.1 (map_pbwFiltration_le R f k)
    · intro x hx
      rw [Submodule.mem_comap, AlgHom.toLinearMap_apply] at hx
      simpa only [map_leftInverse R h x] using map_mem_pbwFiltration R g hx
  rw [hcomap, Submodule.map_comap_eq, inf_comm]

/-- A Lie algebra equivalence maps each PBW filtration step exactly onto the corresponding target
step. -/
@[simp]
theorem mapEquiv_pbwFiltration (e : LieEquiv R L M) (k : ℕ) :
    (pbwFiltration R L k).map (mapEquiv R e).toLinearMap = pbwFiltration R M k := by
  have h : e.toLieHom.comp e.symm.toLieHom = LieHom.id := by
    ext x
    exact e.apply_symm_apply x
  have he : (mapEquiv R e).toLinearMap = (map R e.toLieHom).toLinearMap := by
    ext x
    exact AlgHom.congr_fun (mapEquiv_toAlgHom R e) x
  rw [he]
  exact map_pbwFiltration_eq_of_rightInverse R e.toLieHom e.symm.toLieHom h k

/-- A Lie algebra equivalence maps each preceding PBW filtration step exactly onto the
corresponding preceding target step. -/
@[simp]
theorem mapEquiv_pbwFiltrationPrevious (e : LieEquiv R L M) (k : ℕ) :
    (pbwFiltrationPrevious R L k).map (mapEquiv R e).toLinearMap =
      pbwFiltrationPrevious R M k := by
  cases k with
  | zero => simp
  | succ k => simp

/-- The linear equivalence between the `k`-th PBW filtration steps induced by a Lie algebra
equivalence. -/
noncomputable def mapEquivFiltration (e : LieEquiv R L M) (k : ℕ) :
    pbwFiltration R L k ≃ₗ[R] pbwFiltration R M k :=
  (mapEquiv R e).toLinearEquiv.ofSubmodules _ _ (mapEquiv_pbwFiltration R e k)

/-- The equivalence between PBW filtration steps acts by the enveloping-algebra equivalence. -/
@[simp]
theorem mapEquivFiltration_apply (e : LieEquiv R L M) (k : ℕ)
    (x : pbwFiltration R L k) : mapEquivFiltration R e k x = mapEquiv R e x := by
  rw [mapEquivFiltration, LinearEquiv.ofSubmodules_apply, AlgEquiv.coe_toLinearEquiv]

/-- The identity Lie equivalence induces the identity on each PBW filtration step. -/
@[simp]
theorem mapEquivFiltration_refl (k : ℕ) :
    mapEquivFiltration R (LieEquiv.refl : LieEquiv R L L) k = LinearEquiv.refl R _ := by
  apply LinearEquiv.ext
  intro x
  apply Subtype.ext
  simp only [mapEquivFiltration_apply, mapEquiv_refl, LinearEquiv.refl_apply]
  rfl

/-- Composition of Lie equivalences becomes composition of their equivalences between PBW
filtration steps. -/
@[simp]
theorem mapEquivFiltration_trans (e : LieEquiv R L M) (d : LieEquiv R M N) (k : ℕ) :
    (mapEquivFiltration R e k).trans (mapEquivFiltration R d k) =
      mapEquivFiltration R (e.trans d) k := by
  apply LinearEquiv.ext
  intro x
  apply Subtype.ext
  simp only [LinearEquiv.trans_apply, mapEquivFiltration_apply]
  rw [← mapEquiv_trans, AlgEquiv.trans_apply]

/-- Passing to the inverse Lie equivalence gives the inverse linear equivalence between PBW
filtration steps. -/
@[simp]
theorem mapEquivFiltration_symm (e : LieEquiv R L M) (k : ℕ) :
    (mapEquivFiltration R e k).symm = mapEquivFiltration R e.symm k := by
  apply LinearEquiv.ext
  intro x
  apply (mapEquivFiltration R e k).injective
  rw [LinearEquiv.apply_symm_apply]
  apply Subtype.ext
  simp only [mapEquivFiltration_apply]
  rw [← mapEquiv_symm]
  exact ((mapEquiv R e).apply_symm_apply x).symm

open TauCeti.Algebra.wordFiltration

local notation "ιL" =>
  LieHom.toLinearMap (_root_.UniversalEnvelopingAlgebra.ι R :
    L →ₗ⁅R⁆ _root_.UniversalEnvelopingAlgebra R L)
local notation "ιM" =>
  LieHom.toLinearMap (_root_.UniversalEnvelopingAlgebra.ι R :
    M →ₗ⁅R⁆ _root_.UniversalEnvelopingAlgebra R M)

private noncomputable def mapWordFiltration (f : LieHom R L M) (k : ℕ) :
    TauCeti.Algebra.wordFiltration ιL k →ₗ[R]
      TauCeti.Algebra.wordFiltration ιM k :=
  (map R f).toLinearMap.restrict fun x hx => by
    have hx' : (x : _root_.UniversalEnvelopingAlgebra R L) ∈ pbwFiltration R L k := by
      rwa [pbwFiltration_def]
    simpa only [LinearMap.coe_restrict_apply, AlgHom.toLinearMap_apply, pbwFiltration_def] using
      map_mem_pbwFiltration R f hx'

@[simp]
private theorem mapWordFiltration_id (k : ℕ) :
    mapWordFiltration R (LieHom.id : LieHom R L L) k = LinearMap.id := by
  apply LinearMap.ext
  intro x
  apply Subtype.ext
  simp [mapWordFiltration]

@[simp]
private theorem mapWordFiltration_comp (f : LieHom R L M) (g : LieHom R M N) (k : ℕ) :
    mapWordFiltration R (g.comp f) k =
      (mapWordFiltration R g k).comp (mapWordFiltration R f k) := by
  apply LinearMap.ext
  intro x
  apply Subtype.ext
  simp [mapWordFiltration]

/-- The linear map on the degree-`k` PBW graded pieces induced by a Lie homomorphism. -/
noncomputable def mapGradedPiece (f : LieHom R L M) (k : ℕ) :
    PBWGradedPiece R L k →ₗ[R] PBWGradedPiece R M k :=
  (previousRestricted ιL k).mapQ (previousRestricted ιM k)
    (mapWordFiltration R f k) (by
      intro x hx
      rw [Submodule.mem_comap, mem_previousRestricted_iff]
      rw [mem_previousRestricted_iff] at hx
      have hx' : (x : _root_.UniversalEnvelopingAlgebra R L) ∈
          pbwFiltrationPrevious R L k := by
        rwa [pbwFiltrationPrevious_def]
      simpa only [mapWordFiltration, LinearMap.coe_restrict_apply, AlgHom.toLinearMap_apply,
        pbwFiltrationPrevious_def] using
        map_mem_pbwFiltrationPrevious R f hx')

/-- On quotient representatives, the induced map on a PBW graded piece is the enveloping-algebra
map restricted to the corresponding filtration step. -/
@[simp]
theorem mapGradedPiece_mk (f : LieHom R L M) (k : ℕ)
    (x : TauCeti.Algebra.wordFiltration ιL k) :
    mapGradedPiece R f k (Submodule.Quotient.mk x) =
      Submodule.Quotient.mk
        (⟨TauCeti.UniversalEnvelopingAlgebra.map R f x, by
          have hx : (x : _root_.UniversalEnvelopingAlgebra R L) ∈
              pbwFiltration R L k := by
            rw [pbwFiltration_def]
            exact x.property
          have hmap := map_mem_pbwFiltration R f hx
          rwa [pbwFiltration_def] at hmap⟩ :
          TauCeti.Algebra.wordFiltration ιM k) := by
  rw [mapGradedPiece, Submodule.mapQ_apply]
  apply congrArg Submodule.Quotient.mk
  apply Subtype.ext
  rfl

/-- The identity Lie homomorphism induces the identity on every PBW graded piece. -/
@[simp]
theorem mapGradedPiece_id (k : ℕ) :
    mapGradedPiece R (LieHom.id : LieHom R L L) k = LinearMap.id := by
  unfold mapGradedPiece
  simp only [mapWordFiltration_id]
  exact Submodule.mapQ_id (previousRestricted ιL k)

/-- Composition of Lie homomorphisms becomes composition on each PBW graded piece. -/
@[simp]
theorem mapGradedPiece_comp (f : LieHom R L M) (g : LieHom R M N) (k : ℕ) :
    mapGradedPiece R (g.comp f) k =
      (mapGradedPiece R g k).comp (mapGradedPiece R f k) := by
  unfold mapGradedPiece
  simp only [mapWordFiltration_comp]
  exact Submodule.mapQ_comp _ _ _ _ _ _ _

/-- The induced map on degree zero preserves the homogeneous unit. -/
@[simp]
theorem mapGradedPiece_gradedOne (f : LieHom R L M) :
    mapGradedPiece R f 0
        (gradedOne ιL) = gradedOne ιM := by
  rw [gradedOne_def, mapGradedPiece_mk, gradedOne_def]
  apply congrArg Submodule.Quotient.mk
  apply Subtype.ext
  simp

/-- The maps on PBW graded pieces preserve homogeneous multiplication. -/
@[simp]
theorem mapGradedPiece_gradedMul (f : LieHom R L M) (i j : ℕ)
    (x : PBWGradedPiece R L i) (y : PBWGradedPiece R L j) :
    mapGradedPiece R f (i + j)
        (gradedMul ιL i j x y) =
      gradedMul ιM i j
        (mapGradedPiece R f i x) (mapGradedPiece R f j y) := by
  induction x using Submodule.Quotient.induction_on with
  | _ x =>
      induction y using Submodule.Quotient.induction_on with
      | _ y =>
          rw [gradedMul_apply_mk, mapGradedPiece_mk, mapGradedPiece_mk,
            mapGradedPiece_mk, gradedMul_apply_mk]
          apply congrArg Submodule.Quotient.mk
          apply Subtype.ext
          simp only [map_mul]

/-- The algebra homomorphism of PBW associated gradeds induced by a Lie homomorphism. -/
noncomputable def mapAssociatedGraded (f : LieHom R L M) :
    PBWAssociatedGraded R L →ₐ[R] PBWAssociatedGraded R M :=
  DirectSum.toAlgebra R (PBWGradedPiece R L)
    (fun k => (DirectSum.lof R ℕ (PBWGradedPiece R M) k).comp (mapGradedPiece R f k))
    (by
      simp only [LinearMap.comp_apply, DirectSum.lof_eq_of, gradedGOne_one,
        mapGradedPiece_gradedOne, associatedGraded_of_gradedOne])
    (by
      intro i j x y
      simp only [LinearMap.comp_apply, DirectSum.lof_eq_of, gradedGMul_mul,
        mapGradedPiece_gradedMul, associatedGraded_of_mul_of])

/-- On a homogeneous element, the induced associated-graded map is the map on that graded
piece. -/
@[simp]
theorem mapAssociatedGraded_of (f : LieHom R L M) (k : ℕ) (x : PBWGradedPiece R L k) :
    mapAssociatedGraded R f (DirectSum.of (PBWGradedPiece R L) k x) =
      DirectSum.of (PBWGradedPiece R M) k (mapGradedPiece R f k x) := by
  -- `DirectSum.toAlgebra` is implemented through `DirectSum.toAddMonoid` and has no separate
  -- computation lemma on `DirectSum.of`, so expose that underlying map here.
  change DirectSum.toAddMonoid
      (fun k => ((DirectSum.lof R ℕ (PBWGradedPiece R M) k).comp
        (mapGradedPiece R f k)).toAddMonoidHom)
      (DirectSum.of (PBWGradedPiece R L) k x) = _
  rw [DirectSum.toAddMonoid_of]
  rfl

/-- The identity Lie homomorphism induces the identity on the PBW associated graded. -/
@[simp]
theorem mapAssociatedGraded_id :
    mapAssociatedGraded R (LieHom.id : LieHom R L L) = AlgHom.id R _ := by
  apply DirectSum.algHom_ext
  intro k x
  simp

/-- Composition of Lie homomorphisms becomes composition on PBW associated gradeds. -/
@[simp]
theorem mapAssociatedGraded_comp (f : LieHom R L M) (g : LieHom R M N) :
    mapAssociatedGraded R (g.comp f) =
      (mapAssociatedGraded R g).comp (mapAssociatedGraded R f) := by
  apply DirectSum.algHom_ext
  intro k x
  simp

/-- The associated-graded map sends a degree-one PBW generator to the generator induced by the
original Lie homomorphism. -/
@[simp]
theorem mapAssociatedGraded_pbwGradedGenerator (f : LieHom R L M) (x : L) :
    mapAssociatedGraded R f (pbwGradedGenerator R L x) =
      pbwGradedGenerator R M (f x) := by
  rw [pbwGradedGenerator_apply, mapAssociatedGraded_of, mapGradedPiece_mk,
    pbwGradedGenerator_apply]
  apply congrArg (DirectSum.of (PBWGradedPiece R M) 1)
  apply congrArg Submodule.Quotient.mk
  apply Subtype.ext
  simp

/-- Naturality of the canonical symmetric-algebra map to the PBW associated graded. -/
@[simp]
theorem mapAssociatedGraded_comp_pbwAssociatedGradedMap (f : LieHom R L M) :
    (mapAssociatedGraded R f).comp (pbwAssociatedGradedMap R L) =
      (pbwAssociatedGradedMap R M).comp (SymmetricAlgebra.map R f.toLinearMap) := by
  apply SymmetricAlgebra.algHom_ext
  ext x
  simp

end TauCeti.UniversalEnvelopingAlgebra
