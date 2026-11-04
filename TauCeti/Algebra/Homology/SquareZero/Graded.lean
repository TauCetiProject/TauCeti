/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import Mathlib.LinearAlgebra.Quotient.Bilinear
public import TauCeti.Algebra.Ring.NegOnePow

/-!
# Degree-wise cohomology of a linear endomorphism and products on it

Let `D` be a linear endomorphism of a module `M`, and let `G : ℤ → Submodule R M` be a family of
homogeneous pieces. The degree-`i` cocycles of `D` are the elements of `G i` killed by `D`, the
degree-`i` coboundaries are the images under `D` of elements of `G (i - 1)`, and the degree-`i`
cohomology is the quotient of the first by the second (`LinearMap.cohomology`). This is the
cohomology of the cochain convention, in which a differential raises degree by one.

The definitions need no hypothesis on `D` or `G`; in particular `M` need not be the direct sum of
the pieces `G i`. This covers completed modules, in which a completed combination need not be a
sum of homogeneous ones. Unlike `TauCeti.gradedCochainComplex`, which assembles a differential of
degree one into a cochain complex for Mathlib's categorical homology, these are concrete quotients
whose elements are classes of elements of `M`, in the manner of `LinearMap.homology` (the homology
of a square-zero endomorphism, in `TauCeti.Algebra.Homology.SquareZero`).

A bilinear map `μ : M₁ → M₂ → M₀` which shifts degree by `ε` and obeys the Leibniz rule
`D₀ (μ a b) = μ (D₁ a) b + (-1)^i μ a (D₂ b)` for `a` of degree `i` sends two cocycles to a
cocycle, and a cocycle and a coboundary, in either order, to a coboundary. Hence it descends to a
bilinear map `H^i × H^j → H^k` for `k = i + j + ε` (`LinearMap.cohomologyProduct`).

A linear map `f : M₁ → M₀` which preserves degrees and commutes with the endomorphisms on
homogeneous elements, `D₀ (f a) = f (D₁ a)`, sends cocycles to cocycles and coboundaries to
coboundaries, so it induces a linear map on cohomology in each degree (`LinearMap.cohomologyMap`).
If three such maps intertwine two products up to coboundaries on cocycles, then the induced maps
intertwine the products on cohomology (`LinearMap.cohomologyMap_cohomologyProduct`).

## Main definitions

* `LinearMap.cocycles`, `LinearMap.coboundaries`: the degree-`i` cocycles and coboundaries of a
  linear endomorphism with respect to a family of homogeneous pieces.
* `LinearMap.cohomology`: the degree-`i` cohomology.
* `LinearMap.cohomologyProduct`: the product on cohomology induced by a bilinear map obeying the
  Leibniz rule.
* `LinearMap.cohomologyMap`: the map on cohomology induced by a degree-preserving linear map
  commuting with the endomorphisms.

## Main results

* `LinearMap.coboundaries_le_cocycles`: coboundaries are cocycles for a differential of degree
  one.
* `LinearMap.cohomology_mk_eq_zero_iff`, `LinearMap.cohomology_mk_eq_mk_iff`: when the class of
  a cocycle vanishes, and when two classes are equal.
* `LinearMap.apply_mem_cocycles`, `LinearMap.apply_mem_coboundaries_of_left`,
  `LinearMap.apply_mem_coboundaries_of_right`: products of cocycles are cocycles, and products
  with a coboundary are coboundaries.
* `LinearMap.cohomologyProduct_mk`: the product on cohomology is computed on representing
  cocycles.
* `LinearMap.cohomologyMap_mk`: the induced map on cohomology is computed on representing cocycles.
* `LinearMap.cohomologyMap_id`, `LinearMap.cohomologyMap_comp`: functoriality of the induced maps.
* `LinearMap.cohomologyMap_comp_cohomologyMap`, `LinearMap.cohomologyMap_cohomologyMap`: composites
  of induced maps, in the orientation used by `simp`.
* `LinearMap.cohomologyMap_cohomologyProduct`: maps intertwining two products up to coboundaries
  intertwine the products on cohomology.
-/

public section

noncomputable section

open TauCeti

namespace LinearMap

section Semiring

variable {R M : Type*} [Semiring R] [AddCommMonoid M] [Module R M]
  (D : M →ₗ[R] M) (G : ℤ → Submodule R M) (i : ℤ)

/-- The degree-`i` cocycles of an endomorphism `D` with respect to homogeneous pieces `G`: the
elements of `G i` which `D` sends to zero. -/
def cocycles : Submodule R M :=
  ker D ⊓ G i

/-- The degree-`i` coboundaries of an endomorphism `D` with respect to homogeneous pieces `G`: the
images under `D` of the elements of `G (i - 1)`. -/
def coboundaries : Submodule R M :=
  (G (i - 1)).map D

variable {D G i}

/-- A cocycle of degree `i` is an element of `G i` killed by `D`. -/
@[simp]
theorem mem_cocycles_iff {a : M} : a ∈ D.cocycles G i ↔ D a = 0 ∧ a ∈ G i :=
  Iff.rfl

/-- A coboundary of degree `i` is the image of an element of `G (i - 1)`. -/
@[simp]
theorem mem_coboundaries_iff {a : M} : a ∈ D.coboundaries G i ↔ ∃ x ∈ G (i - 1), D x = a :=
  Iff.rfl

/-- If `D` squares to zero and raises degrees by one on `G (i - 1)`, as a differential of degree
one does, then every degree-`i` coboundary is a cocycle. -/
theorem coboundaries_le_cocycles (hD : ∀ x ∈ G (i - 1), D (D x) = 0)
    (hdeg : ∀ x ∈ G (i - 1), D x ∈ G i) :
    D.coboundaries G i ≤ D.cocycles G i := by
  rintro _ ⟨x, hx, rfl⟩
  exact ⟨hD x hx, hdeg x hx⟩

end Semiring

section Ring

variable {R M : Type*} [Ring R] [AddCommGroup M] [Module R M]
  (D : M →ₗ[R] M) (G : ℤ → Submodule R M) (i : ℤ)

/-- The degree-`i` cohomology of an endomorphism `D` with respect to homogeneous pieces `G`: its
degree-`i` cocycles modulo those which are degree-`i` coboundaries. -/
abbrev cohomology : Type _ :=
  D.cocycles G i ⧸ (D.coboundaries G i).comap (D.cocycles G i).subtype

variable {D G i}

/-- The class of a cocycle vanishes in cohomology exactly when the cocycle is a coboundary. -/
theorem cohomology_mk_eq_zero_iff {a : D.cocycles G i} :
    (Submodule.Quotient.mk a : D.cohomology G i) = 0 ↔ (a : M) ∈ D.coboundaries G i :=
  Submodule.Quotient.mk_eq_zero _

/-- Two cocycles have the same class in cohomology exactly when their difference is a
coboundary. -/
theorem cohomology_mk_eq_mk_iff {a b : D.cocycles G i} :
    (Submodule.Quotient.mk a : D.cohomology G i) = Submodule.Quotient.mk b ↔
      (a - b : M) ∈ D.coboundaries G i :=
  Submodule.Quotient.eq _

end Ring

section Product

variable {R M₁ M₂ M₀ : Type*} [CommRing R] [AddCommGroup M₁] [Module R M₁] [AddCommGroup M₂]
  [Module R M₂] [AddCommGroup M₀] [Module R M₀]
  {D₁ : M₁ →ₗ[R] M₁} {D₂ : M₂ →ₗ[R] M₂} {D₀ : M₀ →ₗ[R] M₀}
  {G₁ : ℤ → Submodule R M₁} {G₂ : ℤ → Submodule R M₂} {G₀ : ℤ → Submodule R M₀}
  (μ : M₁ →ₗ[R] M₂ →ₗ[R] M₀) {ε : ℤ}
  (hdeg : ∀ {i j : ℤ} {a : M₁} {b : M₂}, a ∈ G₁ i → b ∈ G₂ j → μ a b ∈ G₀ (i + j + ε))
  (hL : ∀ {i : ℤ} {a : M₁}, a ∈ G₁ i → ∀ b,
    D₀ (μ a b) = μ (D₁ a) b + negOnePowCast R i • μ a (D₂ b))
  {i j k : ℤ} (hk : i + j + ε = k)

include hdeg hL hk

/-- The product of two cocycles is a cocycle, of the sum of their degrees and the degree shift
of the product. -/
theorem apply_mem_cocycles {a : M₁} {b : M₂} (ha : a ∈ D₁.cocycles G₁ i)
    (hb : b ∈ D₂.cocycles G₂ j) : μ a b ∈ D₀.cocycles G₀ k := by
  subst hk
  rw [mem_cocycles_iff] at ha hb ⊢
  refine ⟨?_, hdeg ha.2 hb.2⟩
  rw [hL ha.2, ha.1, hb.1]
  simp

/-- The product of a coboundary with a cocycle is a coboundary. -/
theorem apply_mem_coboundaries_of_left {a : M₁} {b : M₂} (ha : a ∈ D₁.coboundaries G₁ i)
    (hb : b ∈ D₂.cocycles G₂ j) : μ a b ∈ D₀.coboundaries G₀ k := by
  subst hk
  obtain ⟨x, hx, rfl⟩ := mem_coboundaries_iff.1 ha
  rw [mem_cocycles_iff] at hb
  refine mem_coboundaries_iff.2 ⟨μ x b, ?_, ?_⟩
  · have he : i - 1 + j + ε = i + j + ε - 1 := by ring
    exact he ▸ hdeg hx hb.2
  · rw [hL hx, hb.1]
    simp

/-- The product of a cocycle with a coboundary is a coboundary. -/
theorem apply_mem_coboundaries_of_right {a : M₁} {b : M₂} (ha : a ∈ D₁.cocycles G₁ i)
    (hb : b ∈ D₂.coboundaries G₂ j) : μ a b ∈ D₀.coboundaries G₀ k := by
  subst hk
  obtain ⟨y, hy, rfl⟩ := mem_coboundaries_iff.1 hb
  rw [mem_cocycles_iff] at ha
  refine mem_coboundaries_iff.2 ⟨negOnePowCast R i • μ a y, Submodule.smul_mem _ _ ?_, ?_⟩
  · have he : i + (j - 1) + ε = i + j + ε - 1 := by ring
    exact he ▸ hdeg ha.2 hy
  · rw [map_smul, hL ha.2, ha.1, smul_add, negOnePowCast_smul_negOnePowCast_smul]
    simp

/-- **The product on cohomology.** A bilinear map of degree shift `ε` obeying the Leibniz rule
with the endomorphisms induces a bilinear map from degree-`i` and degree-`j` cohomology to
degree-`k` cohomology, for `k = i + j + ε`. -/
def cohomologyProduct :
    D₁.cohomology G₁ i →ₗ[R] D₂.cohomology G₂ j →ₗ[R] D₀.cohomology G₀ k :=
  liftQ₂ _ _
    ((mk₂ R (fun (a : D₁.cocycles G₁ i) (b : D₂.cocycles G₂ j) =>
        (⟨μ a b, apply_mem_cocycles μ hdeg hL hk a.2 b.2⟩ : D₀.cocycles G₀ k))
      (fun _ _ _ => Subtype.ext (μ.map_add₂ _ _ _))
      (fun _ _ _ => Subtype.ext (μ.map_smul₂ _ _ _))
      (fun _ _ _ => Subtype.ext ((μ _).map_add _ _))
      (fun _ _ _ => Subtype.ext ((μ _).map_smul _ _))).compr₂ (Submodule.mkQ _))
    (fun _ ha => ext fun b => (Submodule.Quotient.mk_eq_zero _).2
      (apply_mem_coboundaries_of_left μ hdeg hL hk ha b.2))
    (fun _ hb => ext fun a => (Submodule.Quotient.mk_eq_zero _).2
      (apply_mem_coboundaries_of_right μ hdeg hL hk a.2 hb))

/-- The product on cohomology of the classes of two cocycles is the class of their product. -/
@[simp]
theorem cohomologyProduct_mk (a : D₁.cocycles G₁ i) (b : D₂.cocycles G₂ j) :
    cohomologyProduct μ hdeg hL hk (Submodule.Quotient.mk a) (Submodule.Quotient.mk b) =
      Submodule.Quotient.mk ⟨μ a b, apply_mem_cocycles μ hdeg hL hk a.2 b.2⟩ :=
  (rfl)

end Product

section Map

variable {R M₁ M₀ : Type*} [Ring R] [AddCommGroup M₁] [Module R M₁] [AddCommGroup M₀]
  [Module R M₀] {D₁ : M₁ →ₗ[R] M₁} {D₀ : M₀ →ₗ[R] M₀}
  {G₁ : ℤ → Submodule R M₁} {G₀ : ℤ → Submodule R M₀} (f : M₁ →ₗ[R] M₀)
  (hdeg : ∀ {i : ℤ} {a : M₁}, a ∈ G₁ i → f a ∈ G₀ i)
  (hD : ∀ {i : ℤ} {a : M₁}, a ∈ G₁ i → D₀ (f a) = f (D₁ a)) {i : ℤ}

include hdeg hD

/-- A degree-preserving map commuting with the endomorphisms sends cocycles to cocycles. -/
theorem apply_mem_cocycles_of_mem_cocycles {a : M₁} (ha : a ∈ D₁.cocycles G₁ i) :
    f a ∈ D₀.cocycles G₀ i := by
  rw [mem_cocycles_iff] at ha ⊢
  exact ⟨by rw [hD ha.2, ha.1, map_zero], hdeg ha.2⟩

/-- A degree-preserving map commuting with the endomorphisms sends coboundaries to
coboundaries. -/
theorem apply_mem_coboundaries_of_mem_coboundaries {a : M₁} (ha : a ∈ D₁.coboundaries G₁ i) :
    f a ∈ D₀.coboundaries G₀ i := by
  obtain ⟨x, hx, rfl⟩ := mem_coboundaries_iff.1 ha
  exact mem_coboundaries_iff.2 ⟨f x, hdeg hx, hD hx⟩

variable (i) in
/-- **The map on cohomology.** A linear map which preserves degrees and commutes with the
endomorphisms on homogeneous elements induces a linear map on degree-`i` cohomology. -/
def cohomologyMap : D₁.cohomology G₁ i →ₗ[R] D₀.cohomology G₀ i :=
  Submodule.mapQ _ _ (f.restrict fun _ ha => apply_mem_cocycles_of_mem_cocycles f hdeg hD ha)
    fun _ ha => apply_mem_coboundaries_of_mem_coboundaries (i := i) f hdeg hD ha

/-- The induced map on cohomology sends the class of a cocycle to the class of its image. -/
@[simp]
theorem cohomologyMap_mk (a : D₁.cocycles G₁ i) :
    cohomologyMap f hdeg hD i (Submodule.Quotient.mk a) =
      Submodule.Quotient.mk ⟨f a, apply_mem_cocycles_of_mem_cocycles f hdeg hD a.2⟩ :=
  (rfl)

omit hdeg hD in
/-- The identity induces the identity on cohomology. -/
@[simp]
theorem cohomologyMap_id :
    cohomologyMap (LinearMap.id : M₁ →ₗ[R] M₁) (G₀ := G₁) (D₀ := D₁) (fun ha => ha)
      (fun _ => rfl) i = LinearMap.id := by
  ext a
  rfl

variable {M₂ : Type*} [AddCommGroup M₂] [Module R M₂] {D₂ : M₂ →ₗ[R] M₂}
  {G₂ : ℤ → Submodule R M₂} (g : M₀ →ₗ[R] M₂)
  (hgdeg : ∀ {i : ℤ} {a : M₀}, a ∈ G₀ i → g a ∈ G₂ i)
  (hgD : ∀ {i : ℤ} {a : M₀}, a ∈ G₀ i → D₂ (g a) = g (D₀ a))

/-- The map induced on cohomology by a composite is the composite of the induced maps. -/
theorem cohomologyMap_comp {hgfdeg : ∀ {i : ℤ} {a : M₁}, a ∈ G₁ i → (g ∘ₗ f) a ∈ G₂ i}
    {hgfD : ∀ {i : ℤ} {a : M₁}, a ∈ G₁ i → D₂ ((g ∘ₗ f) a) = (g ∘ₗ f) (D₁ a)} :
    cohomologyMap (G₁ := G₁) (G₀ := G₂) (g ∘ₗ f) hgfdeg hgfD i =
      cohomologyMap g hgdeg hgD i ∘ₗ cohomologyMap f hdeg hD i := by
  ext a
  rfl

include hgdeg hgD

/-- The composite of two induced maps on cohomology is the map induced by the composite. This is
`cohomologyMap_comp` read right to left, the orientation usable by `simp`: its left-hand side
mentions the intermediate grading `G₀` and endomorphism `D₀`, which the left-hand side of
`cohomologyMap_comp` does not. -/
@[simp]
theorem cohomologyMap_comp_cohomologyMap :
    cohomologyMap g hgdeg hgD i ∘ₗ cohomologyMap f hdeg hD i =
      cohomologyMap (G₁ := G₁) (G₀ := G₂) (g ∘ₗ f) (fun ha => hgdeg (hdeg ha))
        (fun ha => (hgD (hdeg ha)).trans (congrArg g (hD ha))) i :=
  (cohomologyMap_comp f hdeg hD g hgdeg hgD).symm

/-- Applying two induced maps on cohomology in turn is applying the map induced by the
composite. -/
@[simp]
theorem cohomologyMap_cohomologyMap (c : D₁.cohomology G₁ i) :
    cohomologyMap g hgdeg hgD i (cohomologyMap f hdeg hD i c) =
      cohomologyMap (G₁ := G₁) (G₀ := G₂) (g ∘ₗ f) (fun ha => hgdeg (hdeg ha))
        (fun ha => (hgD (hdeg ha)).trans (congrArg g (hD ha))) i c :=
  congr($(cohomologyMap_comp_cohomologyMap f hdeg hD g hgdeg hgD) c)

end Map

section Naturality

variable {R M₁ M₂ M₀ N₁ N₂ N₀ : Type*} [CommRing R]
  [AddCommGroup M₁] [Module R M₁] [AddCommGroup M₂] [Module R M₂]
  [AddCommGroup M₀] [Module R M₀] [AddCommGroup N₁] [Module R N₁]
  [AddCommGroup N₂] [Module R N₂] [AddCommGroup N₀] [Module R N₀]
  {D₁ : M₁ →ₗ[R] M₁} {D₂ : M₂ →ₗ[R] M₂} {D₀ : M₀ →ₗ[R] M₀}
  {E₁ : N₁ →ₗ[R] N₁} {E₂ : N₂ →ₗ[R] N₂} {E₀ : N₀ →ₗ[R] N₀}
  {G₁ : ℤ → Submodule R M₁} {G₂ : ℤ → Submodule R M₂} {G₀ : ℤ → Submodule R M₀}
  {H₁ : ℤ → Submodule R N₁} {H₂ : ℤ → Submodule R N₂} {H₀ : ℤ → Submodule R N₀}
  {μ : M₁ →ₗ[R] M₂ →ₗ[R] M₀} {ν : N₁ →ₗ[R] N₂ →ₗ[R] N₀} {ε : ℤ}
  {hμdeg : ∀ {i j : ℤ} {a : M₁} {b : M₂}, a ∈ G₁ i → b ∈ G₂ j → μ a b ∈ G₀ (i + j + ε)}
  {hμL : ∀ {i : ℤ} {a : M₁}, a ∈ G₁ i → ∀ b,
    D₀ (μ a b) = μ (D₁ a) b + negOnePowCast R i • μ a (D₂ b)}
  {hνdeg : ∀ {i j : ℤ} {a : N₁} {b : N₂}, a ∈ H₁ i → b ∈ H₂ j → ν a b ∈ H₀ (i + j + ε)}
  {hνL : ∀ {i : ℤ} {a : N₁}, a ∈ H₁ i → ∀ b,
    E₀ (ν a b) = ν (E₁ a) b + negOnePowCast R i • ν a (E₂ b)}
  {f₁ : M₁ →ₗ[R] N₁} {f₂ : M₂ →ₗ[R] N₂} {f₀ : M₀ →ₗ[R] N₀}
  {hf₁ : ∀ {i : ℤ} {a : M₁}, a ∈ G₁ i → f₁ a ∈ H₁ i}
  {hf₁D : ∀ {i : ℤ} {a : M₁}, a ∈ G₁ i → E₁ (f₁ a) = f₁ (D₁ a)}
  {hf₂ : ∀ {i : ℤ} {a : M₂}, a ∈ G₂ i → f₂ a ∈ H₂ i}
  {hf₂D : ∀ {i : ℤ} {a : M₂}, a ∈ G₂ i → E₂ (f₂ a) = f₂ (D₂ a)}
  {hf₀ : ∀ {i : ℤ} {a : M₀}, a ∈ G₀ i → f₀ a ∈ H₀ i}
  {hf₀D : ∀ {i : ℤ} {a : M₀}, a ∈ G₀ i → E₀ (f₀ a) = f₀ (D₀ a)}

/-- **Naturality of the product on cohomology.** Let `μ` and `ν` be products inducing products on
cohomology, and let `f₁`, `f₂`, `f₀` be degree-preserving maps commuting with the endomorphisms.
If `f₀ (μ a b) - ν (f₁ a) (f₂ b)` is a coboundary for all cocycles `a` and `b`, then the induced
maps on cohomology intertwine the two products. -/
theorem cohomologyMap_cohomologyProduct {i j k : ℤ} (hk : i + j + ε = k)
    (hnat : ∀ {a : M₁} {b : M₂}, a ∈ D₁.cocycles G₁ i → b ∈ D₂.cocycles G₂ j →
      f₀ (μ a b) - ν (f₁ a) (f₂ b) ∈ E₀.coboundaries H₀ k)
    (x : D₁.cohomology G₁ i) (y : D₂.cohomology G₂ j) :
    cohomologyMap f₀ hf₀ hf₀D k (cohomologyProduct μ hμdeg hμL hk x y) =
      cohomologyProduct ν hνdeg hνL hk (cohomologyMap f₁ hf₁ hf₁D i x)
        (cohomologyMap f₂ hf₂ hf₂D j y) := by
  induction x using Submodule.Quotient.induction_on with | H a => ?_
  induction y using Submodule.Quotient.induction_on with | H b => ?_
  rw [cohomologyProduct_mk, cohomologyMap_mk, cohomologyMap_mk, cohomologyMap_mk,
    cohomologyProduct_mk, cohomology_mk_eq_mk_iff]
  exact hnat a.2 b.2

end Naturality

end LinearMap
