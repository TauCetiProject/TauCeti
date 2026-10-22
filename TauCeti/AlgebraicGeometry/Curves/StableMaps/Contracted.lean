/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.AlgebraicGeometry.Curves.StableMaps.Basic
public import TauCeti.AlgebraicGeometry.Scheme.ConstantOnClosed

/-!
# Components contracted by a prestable map

Let `F : C ⟶ V` be a prestable map to a target `q : V ⟶ S`. An irreducible component `E` of the
source curve `C` is **contracted** by `F` when `F` is constant on `E`, that is, when `F` maps `E`
to a single point. Stability of a prestable map asks for positivity of the log-canonical degree
only on the contracted components of its geometric fibres, so this is the notion the stability
condition is built from. It is meant for fibres: over a geometric point `Spec Ω ⟶ S`, the
components of the geometric fibre contracted by `F` are those of the base change `F.pullback`.

When the base `S` is a Jacobson scheme (for instance the spectrum of a field) and the target is
locally of finite type over `S`, contraction of a component `E` has the following equivalent
forms (the map `F` itself is always locally of finite type, as the source curve is proper):

* `F` maps `E` to a closed point of `V`;
* the closure of the set-theoretic image `F(E)` has Krull dimension zero;
* the restriction of `F` to the reduced induced closed subscheme on `E` factors through
  `Spec κ(v) ⟶ V` for a point `v` of `V`;
* over an algebraically closed field `K`, the restriction of `F` to `E` is the constant map
  through a `K`-point of `V`, exactly as the constant prestable map
  (`TauCeti.AlgebraicGeometry.PrestableMap.const`) is.

Postcomposition with a morphism of targets can only contract more components, and contracts the
same components when the morphism of targets is injective on points, for instance an
immersion such as an isomorphism or a closed immersion. A constant map contracts every component
of a curve over a one-point base.

## Main definitions

* `TauCeti.AlgebraicGeometry.PrestableMap.IsContractedComponent`: an irreducible component of
  the source curve on which the map is constant.

## Main results

In the namespace `TauCeti.AlgebraicGeometry.PrestableMap`:

* `isContractedComponent_iff_topologicalKrullDim_closure_eq_zero`: contraction is dimension zero
  of the image.
* `isContractedComponent_iff_exists_subschemeι_comp_eq`: contraction is factorization of the
  restriction through the residue field of a point.
* `isContractedComponent_iff_exists_subschemeι_comp_eq_section`: over an algebraically closed
  field, contraction is constancy through a rational point.
* `isContractedComponent_postcomp_iff_of_injective`: postcomposition with a morphism of targets
  that is injective on points contracts the same components; `isContractedComponent_postcomp_iff`
  is the case of an immersion.
* `isContractedComponent_const_iff`: a constant map over a one-point base contracts every
  component.

## References

* K. Behrend and Yu. Manin, *Stacks of stable maps and Gromov–Witten invariants*,
  Duke Math. J. 85 (1996), 1–60, Definition 2.1, for the components contracted by a stable map.
* W. Fulton and R. Pandharipande, *Notes on stable maps and quantum cohomology*,
  Proc. Sympos. Pure Math. 62 (1997), Part 2, 45–96, Section 1.
-/

public section

open CategoryTheory TopologicalSpace AlgebraicGeometry

namespace TauCeti.AlgebraicGeometry

universe u

namespace PrestableMap

variable {V W S : Scheme.{u}} {q : V ⟶ S} {n : ℕ} (F : PrestableMap q n)

/-- An irreducible component `E` of the total space of the source curve is **contracted** by the
prestable map `F` when `F` is constant on `E`, that is, maps `E` to at most one point. This is
meant for the components of geometric fibres, that is, for prestable maps over the spectrum of an
algebraically closed field. -/
def IsContractedComponent (E : Set F.curve.total) : Prop :=
  E ∈ irreducibleComponents F.curve.total ∧ (F.map '' E).Subsingleton

/-- Restatement of the definition of a contracted component. -/
theorem isContractedComponent_iff {E : Set F.curve.total} :
    F.IsContractedComponent E ↔
      E ∈ irreducibleComponents F.curve.total ∧ (F.map '' E).Subsingleton :=
  Iff.rfl

variable {F} in
/-- A contracted component is an irreducible component. -/
theorem IsContractedComponent.mem_irreducibleComponents {E : Set F.curve.total}
    (h : F.IsContractedComponent E) : E ∈ irreducibleComponents F.curve.total :=
  h.1

variable {F} in
/-- The map is constant on a contracted component. -/
theorem IsContractedComponent.subsingleton_image {E : Set F.curve.total}
    (h : F.IsContractedComponent E) : (F.map '' E).Subsingleton :=
  h.2

section Jacobson

variable [JacobsonSpace S] [LocallyOfFiniteType q]

variable {F} in
/-- Over a Jacobson base, for instance the spectrum of a field, a contracted component is mapped
to a closed point of the target. -/
theorem IsContractedComponent.exists_isClosed_singleton_image_eq {E : Set F.curve.total}
    (h : F.IsContractedComponent E) : ∃ v, IsClosed {v} ∧ F.map '' E = {v} :=
  have := LocallyOfFiniteType.jacobsonSpace q
  F.map.exists_isClosed_singleton_image_eq
    (isClosed_of_mem_irreducibleComponents E h.1).isLocallyClosed h.1.1.nonempty h.2

/-- Over a Jacobson base, for instance the spectrum of a field, an irreducible component is
contracted exactly when the closure of its image has Krull dimension zero. -/
theorem isContractedComponent_iff_topologicalKrullDim_closure_eq_zero {E : Set F.curve.total}
    (hE : E ∈ irreducibleComponents F.curve.total) :
    F.IsContractedComponent E ↔ topologicalKrullDim (closure (F.map '' E)) = 0 :=
  have := LocallyOfFiniteType.jacobsonSpace q
  (and_iff_right hE).trans <| F.map.subsingleton_image_iff_topologicalKrullDim_closure_eq_zero
    (isClosed_of_mem_irreducibleComponents E hE).isLocallyClosed hE.1

/-- Over a Jacobson base, for instance the spectrum of a field, an irreducible component `E` is
contracted exactly when the restriction of the map to the reduced induced closed subscheme on `E`
factors through `Spec κ(v) ⟶ V` for some point `v` of the target. -/
theorem isContractedComponent_iff_exists_subschemeι_comp_eq {E : Closeds F.curve.total}
    (hE : (E : Set F.curve.total) ∈ irreducibleComponents F.curve.total) :
    F.IsContractedComponent E ↔ ∃ (v : V) (g : (Scheme.IdealSheafData.vanishingIdeal E).subscheme ⟶
      Spec (V.residueField v)),
      (Scheme.IdealSheafData.vanishingIdeal E).subschemeι ≫ F.map =
        g ≫ V.fromSpecResidueField v :=
  have := LocallyOfFiniteType.jacobsonSpace q
  (and_iff_right hE).trans <|
    F.map.subsingleton_image_iff_exists_subschemeι_comp_eq hE.1.nonempty

end Jacobson

/-- Over an algebraically closed field `K`, with the target locally of finite type over `K`, an
irreducible component `E` is contracted exactly when the restriction of the map to the reduced
induced closed subscheme on `E` is the constant map through a `K`-point `σ` of the target. -/
theorem isContractedComponent_iff_exists_subschemeι_comp_eq_section {K : Type u} [Field K]
    [IsAlgClosed K] {q : V ⟶ Spec (.of K)} [LocallyOfFiniteType q] (F : PrestableMap q n)
    {E : Closeds F.curve.total}
    (hE : (E : Set F.curve.total) ∈ irreducibleComponents F.curve.total) :
    F.IsContractedComponent E ↔ ∃ σ : Spec (.of K) ⟶ V, σ ≫ q = 𝟙 _ ∧
      (Scheme.IdealSheafData.vanishingIdeal E).subschemeι ≫ F.map =
        (Scheme.IdealSheafData.vanishingIdeal E).subschemeι ≫ F.curve.toBase ≫ σ := by
  rw [isContractedComponent_iff, and_iff_right hE,
    F.map.subsingleton_image_iff_exists_subschemeι_comp_eq_section q hE.1.nonempty]
  simp only [w_assoc]

/-- The image of a set under the map of a postcomposed prestable map is its image under the
original map, pushed forward along the morphism of targets. -/
theorem image_postcomp_map {r : W ⟶ S} (h : V ⟶ W) (hh : h ≫ r = q) (E : Set F.curve.total) :
    (F.postcomp h hh).map '' E = h '' (F.map '' E) := by
  rw [Set.image_image]
  -- The source curve of `F.postcomp h hh` is that of `F`, and its map is `F.map ≫ h`
  -- (`postcomp_curve`, `postcomp_map`); the pointwise identity is stated on that curve.
  exact Set.image_congr fun x _ ↦ Scheme.Hom.comp_apply F.map h x

variable {F} in
/-- Postcomposition with a morphism of targets contracts every component the map contracts. -/
theorem IsContractedComponent.postcomp {r : W ⟶ S} (h : V ⟶ W) (hh : h ≫ r = q)
    {E : Set F.curve.total} (hF : F.IsContractedComponent E) :
    (F.postcomp h hh).IsContractedComponent E :=
  ⟨hF.1, (F.image_postcomp_map h hh E).symm ▸ hF.2.image _⟩

/-- Postcomposition with a morphism of targets that is injective on points contracts the same
components. -/
theorem isContractedComponent_postcomp_iff_of_injective {r : W ⟶ S} (h : V ⟶ W)
    (hinj : Function.Injective h) (hh : h ≫ r = q) {E : Set F.curve.total} :
    (F.postcomp h hh).IsContractedComponent E ↔ F.IsContractedComponent E :=
  and_congr Iff.rfl <| by rw [image_postcomp_map, hinj.subsingleton_image_iff]

/-- Postcomposition with an immersion of targets, for instance an isomorphism or a closed
immersion, contracts the same components. -/
@[simp]
theorem isContractedComponent_postcomp_iff {r : W ⟶ S} (h : V ⟶ W) [IsPreimmersion h]
    (hh : h ≫ r = q) {E : Set F.curve.total} :
    (F.postcomp h hh).IsContractedComponent E ↔ F.IsContractedComponent E :=
  F.isContractedComponent_postcomp_iff_of_injective h h.isEmbedding.injective hh

/-- A constant prestable map over a one-point base, for instance the spectrum of a field,
contracts every irreducible component of its source curve. -/
@[simp]
theorem isContractedComponent_const_iff [Subsingleton S] (P : PointedPrestableFamily S n)
    (σ : S ⟶ V) (hσ : σ ≫ q = 𝟙 S) {E : Set P.total} :
    (const P σ hσ).IsContractedComponent E ↔ E ∈ irreducibleComponents P.total := by
  refine and_iff_left_of_imp fun _ ↦ ?_
  rintro _ ⟨a, -, rfl⟩ _ ⟨b, -, rfl⟩
  simp only [const_map]
  exact congr(σ $(Subsingleton.elim _ _))

end PrestableMap

end TauCeti.AlgebraicGeometry
