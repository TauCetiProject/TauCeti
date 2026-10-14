/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import Mathlib.Algebra.Category.ModuleCat.Basic
public import Mathlib.Algebra.Homology.HomologicalComplex
public import Mathlib.LinearAlgebra.Quotient.Basic
public import TauCeti.AlgebraicTopology.Singular.Cubical.LocalCoefficients.Chains

/-!
# Normalized cubical chains with local coefficients

Let `L` be a local coefficient system on a space `X`.  The **degenerate chains** with coefficients
in `L` are the sums of the summands of the degenerate cubes, and the **normalized cubical chains**
`C^□_n(X; L)` are the cubical chains with coefficients in `L` modulo the degenerate ones.  They are
the chains with local coefficients of Serre, *Homologie singulière des espaces fibrés*,
Chapter II, in Massey's convention for degeneracy, and they extend the normalized cubical chains
of `TauCeti.AlgebraicTopology.Singular.Cubical.Normalized` from constant coefficients to local
ones.

The degenerate chains form a subcomplex.  On a cube `c` which does not depend on its coordinate
`i`, every face of `c` in another coordinate is degenerate, and the two faces in the coordinate
`i` coincide, with the same transported coefficient: writing `c` as a degeneracy `s ∘ π`, both
faces are the subcube `s` of `c`, and the transport inside `c` is the transport inside `s`.

The boundary, the maps induced by morphisms of local systems and by continuous maps, and the
augmentation all descend to the normalized chains, and they assemble into a chain complex of
modules `L.normalizedTwistedCubicalChainComplex` with chain maps between such complexes.

## Main definitions

* `TauCeti.LocalCoefficientSystem.TwistedCubicalChain.degenerate L n`: the degenerate chains.
* `TauCeti.LocalCoefficientSystem.NormalizedTwistedCubicalChain L n`: the normalized cubical
  chains.
* `TauCeti.LocalCoefficientSystem.NormalizedTwistedCubicalChain.boundary`, `.coefficientMap`,
  `.map`, `.augment`: the induced boundary, functoriality and augmentation.
* `TauCeti.LocalCoefficientSystem.normalizedTwistedCubicalChainComplex L`: the normalized cubical
  chain complex with coefficients in `L`, with the chain maps
  `TauCeti.LocalCoefficientSystem.normalizedTwistedCubicalChainComplexCoefficientMap η` and
  `TauCeti.LocalCoefficientSystem.normalizedTwistedCubicalChainComplexMap f L`.

## Main results

* `TauCeti.LocalCoefficientSystem.TwistedCubicalChain.boundary_ofCube_mem_degenerate`,
  `TauCeti.LocalCoefficientSystem.TwistedCubicalChain.degenerate_le_comap_boundary`: the
  degenerate chains form a subcomplex.
* `TauCeti.LocalCoefficientSystem.NormalizedTwistedCubicalChain.boundary_boundary`: `∂ ∘ ∂ = 0`.
* `TauCeti.LocalCoefficientSystem.NormalizedTwistedCubicalChain.augment_boundary`: `ε ∘ ∂ = 0`.
* `TauCeti.LocalCoefficientSystem.normalizedTwistedCubicalChainComplexMap_id`,
  `TauCeti.LocalCoefficientSystem.normalizedTwistedCubicalChainComplexMap_comp`: functoriality.

## References

* J.-P. Serre, *Homologie singulière des espaces fibrés. Applications*, Ann. of Math. 54 (1951),
  Chapter II.
* W. S. Massey, *Singular Homology Theory*, GTM 70, Springer, 1980, Chapters II and XIV.
* J.-F. Barraud, M. Damian, V. Humilière, A. Oancea, *Floer homology with DG coefficients.
  Applications to cotangent bundles*, arXiv:2404.07953, §7.2.
-/

public section

noncomputable section

open CategoryTheory Limits unitInterval

universe u v w

namespace TauCeti

namespace LocalCoefficientSystem

open SingularCube
open ContinuousMap (pathClass pathClass_self pathClass_comp_pathClass)

variable {R : Type u} [Ring R] {X Y Z : TopCat.{v}}

namespace TwistedCubicalChain

section Degenerate

variable (L : LocalCoefficientSystem.{u, v, w} R X)

/-- The **degenerate `n`-chains** with coefficients in `L`: the sum of the summands of the
degenerate `n`-cubes. -/
def degenerate (n : ℕ) : Submodule R (L.TwistedCubicalChain n) :=
  ⨆ (c : SingularCube X n) (_ : IsDegenerate c), LinearMap.range (ofCube L c)

variable {L}

/-- A degenerate cube with any coefficient is a degenerate chain. -/
theorem ofCube_mem_degenerate {n : ℕ} {c : SingularCube X n} (hc : IsDegenerate c)
    (a : L.obj (FundamentalGroupoid.mk (c 0))) : ofCube L c a ∈ degenerate L n := by
  rw [degenerate]
  exact Submodule.mem_iSup_of_mem c (Submodule.mem_iSup_of_mem hc ⟨a, rfl⟩)

/-- A degenerate subcube with any coefficient is a degenerate chain. -/
theorem ofSubcube_mem_degenerate {m n : ℕ} {c : SingularCube X n} {ι : C(Fin m → I, Fin n → I)}
    (hc : IsDegenerate (c.comp ι)) (a : L.obj (FundamentalGroupoid.mk (c 0))) :
    ofSubcube L c ι a ∈ degenerate L m := by
  rw [ofSubcube_apply]
  exact ofCube_mem_degenerate hc _

/-- A submodule contains the degenerate chains as soon as it contains every degenerate cube with
every coefficient. -/
theorem degenerate_le {n : ℕ} {p : Submodule R (L.TwistedCubicalChain n)}
    (h : ∀ c : SingularCube X n, IsDegenerate c → ∀ a, ofCube L c a ∈ p) : degenerate L n ≤ p := by
  rw [degenerate]
  exact iSup₂_le fun c hc ↦ by
    rintro _ ⟨a, rfl⟩
    exact h c hc a

variable (L) in
/-- There are no degenerate `0`-chains: a `0`-cube is a point. -/
@[simp]
theorem degenerate_zero : degenerate L 0 = ⊥ :=
  le_bot_iff.1 (degenerate_le fun c hc ↦ (not_isDegenerate_zero c hc).elim)

/-- Subcubes of a degeneracy `s ∘ π` along two maps which agree after `π` carry the same
coefficient. -/
private theorem ofSubcube_eq_of_comp_eq {m n k : ℕ} (s : SingularCube X k)
    (π : C(Fin n → I, Fin k → I)) {c : SingularCube X n} (hc : s.comp π = c)
    {ι ι' : C(Fin m → I, Fin n → I)} (h : π.comp ι = π.comp ι') :
    ofSubcube L c ι = ofSubcube L c ι' := by
  subst hc
  refine LinearMap.ext fun a ↦ ?_
  obtain ⟨b, rfl⟩ : ∃ b, L.map (pathClass s 0 (π 0)) b = a := by
    refine ⟨L.map (pathClass s (π 0) 0) a, ?_⟩
    rw [← ModuleCat.comp_apply, ← L.map_comp, pathClass_comp_pathClass, pathClass_self,
      L.map_id, ModuleCat.id_apply]
  rw [ofSubcube_comp, ofSubcube_comp, h]

/-- The boundary of a degenerate cube is a degenerate chain: the two terms of a coordinate the
cube does not depend on cancel, and every other face is degenerate. -/
theorem boundary_ofCube_mem_degenerate {n : ℕ} {c : SingularCube X (n + 1)}
    (hc : IsDegenerate c) (a : L.obj (FundamentalGroupoid.mk (c 0))) :
    boundary L n (ofCube L c a) ∈ degenerate L n := by
  obtain ⟨i, s, hs⟩ := isDegenerate_iff_exists_eq_degeneracy.1 hc
  have hπ : s.comp (degeneracy (ContinuousMap.id _) i) = c := by
    rw [← degeneracy_comp, ContinuousMap.comp_id, hs]
  have hi : IsDegenerateAt c i := hs ▸ isDegenerateAt_degeneracy s i
  rw [boundary_ofCube]
  refine Submodule.sum_mem _ fun j _ ↦ Submodule.smul_of_tower_mem _ _ ?_
  by_cases hij : i = j
  · subst hij
    have h : (degeneracy (ContinuousMap.id (Fin n → I)) i).comp (face i 0 (ContinuousMap.id _)) =
        (degeneracy (ContinuousMap.id (Fin n → I)) i).comp (face i 1 (ContinuousMap.id _)) := by
      rw [comp_face_id, comp_face_id, face_degeneracy_self, face_degeneracy_self]
    rw [ofSubcube_eq_of_comp_eq s _ hπ h, sub_self]
    exact Submodule.zero_mem _
  · refine Submodule.sub_mem _ (ofSubcube_mem_degenerate ?_ a) (ofSubcube_mem_degenerate ?_ a)
    · rw [comp_face_id]
      exact isDegenerate_face_of_ne hi hij 0
    · rw [comp_face_id]
      exact isDegenerate_face_of_ne hi hij 1

/-- The degenerate chains form a subcomplex. -/
theorem degenerate_le_comap_boundary (n : ℕ) :
    degenerate L (n + 1) ≤ (degenerate L n).comap (boundary L n) :=
  degenerate_le fun _ hc a ↦ boundary_ofCube_mem_degenerate hc a

/-- A morphism of local systems preserves degenerate chains. -/
theorem degenerate_le_comap_coefficientMap {K : LocalCoefficientSystem.{u, v, w} R X}
    (η : L ⟶ K) (n : ℕ) : degenerate L n ≤ (degenerate K n).comap (coefficientMap η n) :=
  degenerate_le fun c hc a ↦ by
    rw [Submodule.mem_comap, coefficientMap_ofCube]
    exact ofCube_mem_degenerate hc _

/-- A continuous map preserves degenerate chains. -/
theorem degenerate_le_comap_map (f : C(X, Y)) (L : LocalCoefficientSystem.{u, v, w} R Y)
    (n : ℕ) : degenerate ((pullback f).obj L) n ≤ (degenerate L n).comap (map f L n) :=
  degenerate_le fun c hc a ↦ by
    rw [Submodule.mem_comap, map_ofCube]
    exact ofCube_mem_degenerate (hc.comp f) _

end Degenerate

end TwistedCubicalChain

/-- The **normalized cubical `n`-chains with coefficients in a local system** `L`: the cubical
chains with coefficients in `L` modulo the degenerate ones. -/
abbrev NormalizedTwistedCubicalChain (L : LocalCoefficientSystem.{u, v, w} R X) (n : ℕ) :
    Type (max v w) :=
  L.TwistedCubicalChain n ⧸ TwistedCubicalChain.degenerate L n

namespace NormalizedTwistedCubicalChain


section Basic

variable (L : LocalCoefficientSystem.{u, v, w} R X)

/-- The class of a singular cube with a coefficient in the normalized chains. -/
def ofCube {n : ℕ} (c : SingularCube X n) :
    L.obj (FundamentalGroupoid.mk (c 0)) →ₗ[R] L.NormalizedTwistedCubicalChain n :=
  (TwistedCubicalChain.degenerate L n).mkQ ∘ₗ TwistedCubicalChain.ofCube L c

variable {L}

/-- The class of a cube with a coefficient is the class of the corresponding unnormalized chain. -/
theorem ofCube_apply {n : ℕ} (c : SingularCube X n) (a : L.obj (FundamentalGroupoid.mk (c 0))) :
    ofCube L c a = Submodule.Quotient.mk (TwistedCubicalChain.ofCube L c a) := by
  rw [ofCube, LinearMap.comp_apply, Submodule.mkQ_apply]

/-- A degenerate cube is zero in the normalized chains. -/
@[simp]
theorem ofCube_eq_zero {n : ℕ} {c : SingularCube X n} (hc : IsDegenerate c)
    (a : L.obj (FundamentalGroupoid.mk (c 0))) : ofCube L c a = 0 := by
  rw [ofCube_apply, Submodule.Quotient.mk_eq_zero]
  exact TwistedCubicalChain.ofCube_mem_degenerate hc a

/-- Two linear maps out of the normalized chains agree as soon as they agree on every cube. -/
@[ext]
theorem hom_ext {n : ℕ} {N : Type*} [AddCommGroup N] [Module R N]
    {f g : L.NormalizedTwistedCubicalChain n →ₗ[R] N} (h : ∀ c, f ∘ₗ ofCube L c = g ∘ₗ ofCube L c) :
    f = g :=
  Submodule.linearMap_qext _ (TwistedCubicalChain.hom_ext fun c ↦ by
    have hc := h c
    rwa [ofCube, ← LinearMap.comp_assoc, ← LinearMap.comp_assoc] at hc)

end Basic

section Boundary

variable (L : LocalCoefficientSystem.{u, v, w} R X)

/-- The boundary of normalized cubical chains with coefficients in `L`. -/
def boundary (n : ℕ) :
    L.NormalizedTwistedCubicalChain (n + 1) →ₗ[R] L.NormalizedTwistedCubicalChain n :=
  Submodule.mapQ _ _ (TwistedCubicalChain.boundary L n)
    (TwistedCubicalChain.degenerate_le_comap_boundary n)

variable {L}

/-- The boundary of the class of a chain is the class of its boundary. -/
@[simp]
theorem boundary_mk {n : ℕ} (x : L.TwistedCubicalChain (n + 1)) :
    boundary L n (Submodule.Quotient.mk x) =
      Submodule.Quotient.mk (TwistedCubicalChain.boundary L n x) :=
  by rw [boundary, Submodule.mapQ_apply]

variable (L) in
/-- The boundary of a boundary vanishes. -/
theorem boundary_boundary (n : ℕ) : boundary L n ∘ₗ boundary L (n + 1) = 0 := by
  rw [boundary, boundary, ← Submodule.mapQ_comp]
  simp only [TwistedCubicalChain.boundary_boundary, Submodule.mapQ_zero]

end Boundary

section CoefficientMap

variable {L K J : LocalCoefficientSystem.{u, v, w} R X}

/-- The map of normalized cubical chains induced by a morphism of local systems. -/
def coefficientMap (η : L ⟶ K) (n : ℕ) :
    L.NormalizedTwistedCubicalChain n →ₗ[R] K.NormalizedTwistedCubicalChain n :=
  Submodule.mapQ _ _ (TwistedCubicalChain.coefficientMap η n)
    (TwistedCubicalChain.degenerate_le_comap_coefficientMap η n)

/-- The map induced by a morphism of local systems on the class of a chain. -/
@[simp]
theorem coefficientMap_mk (η : L ⟶ K) {n : ℕ} (x : L.TwistedCubicalChain n) :
    coefficientMap η n (Submodule.Quotient.mk x) =
      Submodule.Quotient.mk (TwistedCubicalChain.coefficientMap η n x) := by
  rw [coefficientMap, Submodule.mapQ_apply]

/-- A morphism of local systems acts on the class of a cube by its component at the origin. -/
@[simp]
theorem coefficientMap_ofCube (η : L ⟶ K) {n : ℕ} (c : SingularCube X n)
    (a : L.obj (FundamentalGroupoid.mk (c 0))) :
    coefficientMap η n (ofCube L c a) = ofCube K c (η.app _ a) := by
  rw [ofCube_apply, ofCube_apply, coefficientMap_mk, TwistedCubicalChain.coefficientMap_ofCube]

/-- The identity of a local system induces the identity on normalized chains. -/
@[simp]
theorem coefficientMap_id (n : ℕ) : coefficientMap (𝟙 L) n = LinearMap.id :=
  hom_ext fun c ↦ LinearMap.ext fun a ↦ by simp

/-- A composite of morphisms of local systems induces the composite map on normalized chains. -/
theorem coefficientMap_comp (η : L ⟶ K) (θ : K ⟶ J) (n : ℕ) :
    coefficientMap (η ≫ θ) n = coefficientMap θ n ∘ₗ coefficientMap η n :=
  hom_ext fun c ↦ LinearMap.ext fun a ↦ by simp

/-- The boundary commutes with the maps induced by a morphism of local systems. -/
theorem coefficientMap_boundary (η : L ⟶ K) (n : ℕ) :
    coefficientMap η n ∘ₗ boundary L n = boundary K n ∘ₗ coefficientMap η (n + 1) := by
  rw [coefficientMap, coefficientMap, boundary, boundary, ← Submodule.mapQ_comp,
    ← Submodule.mapQ_comp]
  simp only [TwistedCubicalChain.coefficientMap_boundary]

end CoefficientMap

section Map

variable (f : C(X, Y)) (L : LocalCoefficientSystem.{u, v, w} R Y)

/-- The map of normalized cubical chains induced by a continuous map `f`, from the chains with
coefficients in the pulled back system `f⁎L` to the chains with coefficients in `L`. -/
def map (n : ℕ) :
    ((pullback f).obj L).NormalizedTwistedCubicalChain n →ₗ[R] L.NormalizedTwistedCubicalChain n :=
  Submodule.mapQ _ _ (TwistedCubicalChain.map f L n)
    (TwistedCubicalChain.degenerate_le_comap_map f L n)

variable {f L}

/-- The map induced by a continuous map on the class of a chain. -/
@[simp]
theorem map_mk {n : ℕ} (x : ((pullback f).obj L).TwistedCubicalChain n) :
    map f L n (Submodule.Quotient.mk x) =
      Submodule.Quotient.mk (TwistedCubicalChain.map f L n x) := by
  rw [map, Submodule.mapQ_apply]

/-- A continuous map sends the class of a cube to the class of the image cube. -/
theorem map_ofCube {n : ℕ} (c : SingularCube X n)
    (a : ((pullback f).obj L).obj (FundamentalGroupoid.mk (c 0))) :
    map f L n (ofCube _ c a) = ofCube L (f.comp c) a := by
  rw [ofCube_apply, map_mk, TwistedCubicalChain.map_ofCube]
  exact (ofCube_apply (L := L) (f.comp c) a).symm

variable (f L) in
/-- The boundary is natural. -/
theorem map_boundary (n : ℕ) :
    map f L n ∘ₗ boundary ((pullback f).obj L) n = boundary L n ∘ₗ map f L (n + 1) := by
  rw [map, map, boundary, boundary, ← Submodule.mapQ_comp, ← Submodule.mapQ_comp]
  simp only [TwistedCubicalChain.map_boundary]

/-- The map induced by a continuous map is natural in the coefficient system. -/
theorem coefficientMap_map {K : LocalCoefficientSystem.{u, v, w} R Y} (η : L ⟶ K) (n : ℕ) :
    coefficientMap η n ∘ₗ map f L n = map f K n ∘ₗ coefficientMap ((pullback f).map η) n := by
  rw [coefficientMap, coefficientMap, map, map, ← Submodule.mapQ_comp, ← Submodule.mapQ_comp]
  simp only [TwistedCubicalChain.coefficientMap_map]

/-- The identity map induces on normalized chains the map coming from the identification of a
system with its pullback along the identity. -/
@[simp]
theorem map_id (L : LocalCoefficientSystem.{u, v, w} R X) (n : ℕ) :
    map (ContinuousMap.id X) L n = coefficientMap ((pullbackIdIso X).hom.app L) n := by
  rw [map, coefficientMap]
  simp only [TwistedCubicalChain.map_id]
  rfl

/-- A composite of continuous maps induces on normalized chains the composite of the two induced
maps, after the identification of the pullback along the composite with the iterated
pullback. -/
theorem map_comp (g : C(Y, Z)) (L : LocalCoefficientSystem.{u, v, w} R Z) (n : ℕ) :
    map (g.comp f) L n = map g L n ∘ₗ map f ((pullback g).obj L) n ∘ₗ
      coefficientMap ((pullbackCompIso f g).hom.app L) n := by
  refine LinearMap.ext fun x ↦ Submodule.Quotient.induction_on _ x fun x ↦ ?_
  simp only [LinearMap.comp_apply, map_mk, coefficientMap_mk, TwistedCubicalChain.map_comp]

end Map

section Augment

variable {L : LocalCoefficientSystem.{u, v, w} R X}

/-- The **augmentation** of the normalized `0`-chains into a cocone `s` over the local system. -/
def augment (s : Cocone L) : L.NormalizedTwistedCubicalChain 0 →ₗ[R] s.pt :=
  Submodule.liftQ _ (TwistedCubicalChain.augment s)
    (by rw [TwistedCubicalChain.degenerate_zero]; exact bot_le)

/-- The augmentation of the class of a `0`-chain is its augmentation. -/
@[simp]
theorem augment_mk (s : Cocone L) (x : L.TwistedCubicalChain 0) :
    augment s (Submodule.Quotient.mk x) = TwistedCubicalChain.augment s x := by
  rw [augment, Submodule.liftQ_apply]

/-- The augmentation of a point with a coefficient is the image of the coefficient in the cocone. -/
@[simp]
theorem augment_ofCube (s : Cocone L) (c : SingularCube X 0)
    (a : L.obj (FundamentalGroupoid.mk (c 0))) :
    augment s (ofCube L c a) = s.ι.app _ a := by
  rw [ofCube_apply, augment_mk, TwistedCubicalChain.augment_ofCube]

/-- The augmentation vanishes on boundaries. -/
theorem augment_boundary (s : Cocone L) : augment s ∘ₗ boundary L 0 = 0 := by
  refine Submodule.linearMap_qext _ ?_
  rw [LinearMap.zero_comp, LinearMap.comp_assoc, boundary, Submodule.mapQ_mkQ,
    ← LinearMap.comp_assoc, augment, Submodule.liftQ_mkQ, TwistedCubicalChain.augment_boundary]

/-- The augmentation is natural in the coefficient system. -/
theorem augment_coefficientMap {K : LocalCoefficientSystem.{u, v, w} R X} (η : L ⟶ K)
    (s : Cocone K) :
    augment s ∘ₗ coefficientMap η 0 = augment ((Cocone.precompose η).obj s) :=
  hom_ext fun c ↦ LinearMap.ext fun a ↦ by simp

/-- The augmentation is natural in the space. -/
theorem augment_map (f : C(X, Y)) {L : LocalCoefficientSystem.{u, v, w} R Y} (s : Cocone L) :
    augment s ∘ₗ map f L 0 = augment (s.whisker (FundamentalGroupoid.map f)) :=
  hom_ext fun c ↦ LinearMap.ext fun a ↦ (congrArg (augment s) (map_ofCube c a)).trans
    ((augment_ofCube (L := L) s (f.comp c) a).trans
      (augment_ofCube (s.whisker (FundamentalGroupoid.map f)) c a).symm)

end Augment

end NormalizedTwistedCubicalChain

section ChainComplex

open NormalizedTwistedCubicalChain

-- Exposed, like `TauCeti.normalizedCubicalChainComplex`, so that the term `X n` is definitionally
-- `ModuleCat.of R (L.NormalizedTwistedCubicalChain n)`: the chain maps to and from
-- `twistedChainComplex` in the comparison are built from linear maps on the normalized chains.
/-- The **normalized cubical chain complex with coefficients in a local system** `L`. -/
@[expose] def normalizedTwistedCubicalChainComplex (L : LocalCoefficientSystem.{u, v, w} R X) :
    ChainComplex (ModuleCat.{max v w} R) ℕ :=
  ChainComplex.of (fun n ↦ ModuleCat.of R (L.NormalizedTwistedCubicalChain n))
    (fun n ↦ ModuleCat.ofHom (boundary L n)) fun n ↦ by
      rw [← ModuleCat.ofHom_comp, boundary_boundary]
      rfl

/-- The terms of the normalized cubical chain complex are the normalized chains. -/
@[simp]
theorem normalizedTwistedCubicalChainComplex_X (L : LocalCoefficientSystem.{u, v, w} R X) (n : ℕ) :
    L.normalizedTwistedCubicalChainComplex.X n =
      ModuleCat.of R (L.NormalizedTwistedCubicalChain n) :=
  (rfl)

/-- The differential of the normalized cubical chain complex is the boundary. -/
@[simp]
theorem normalizedTwistedCubicalChainComplex_d_apply (L : LocalCoefficientSystem.{u, v, w} R X)
    (n : ℕ)
    (x : L.NormalizedTwistedCubicalChain (n + 1)) :
    L.normalizedTwistedCubicalChainComplex.d (n + 1) n x = boundary L n x := by
  simp only [normalizedTwistedCubicalChainComplex, ChainComplex.of_d]
  rfl

/-- The chain map of normalized cubical chain complexes induced by a morphism of local
systems. -/
def normalizedTwistedCubicalChainComplexCoefficientMap {L K : LocalCoefficientSystem.{u, v, w} R X}
    (η : L ⟶ K) : L.normalizedTwistedCubicalChainComplex ⟶ K.normalizedTwistedCubicalChainComplex :=
  ChainComplex.ofHom (fun n ↦ ModuleCat.ofHom (coefficientMap η n)) fun n ↦ by
    simp only [normalizedTwistedCubicalChainComplex, ChainComplex.of_d, ← ModuleCat.ofHom_comp,
      coefficientMap_boundary]

/-- The components of the chain map induced by a morphism of local systems. -/
@[simp]
theorem normalizedTwistedCubicalChainComplexCoefficientMap_f
    {L K : LocalCoefficientSystem.{u, v, w} R X} (η : L ⟶ K) (n : ℕ) :
    (normalizedTwistedCubicalChainComplexCoefficientMap η).f n =
      ModuleCat.ofHom (coefficientMap η n) := by
  unfold normalizedTwistedCubicalChainComplexCoefficientMap
  rfl

/-- The chain map of normalized cubical chain complexes induced by a continuous map `f`, from the
complex with coefficients in `f⁎L` to the complex with coefficients in `L`. -/
def normalizedTwistedCubicalChainComplexMap (f : C(X, Y))
    (L : LocalCoefficientSystem.{u, v, w} R Y) :
    ((pullback f).obj L).normalizedTwistedCubicalChainComplex ⟶
      L.normalizedTwistedCubicalChainComplex :=
  ChainComplex.ofHom (fun n ↦ ModuleCat.ofHom (map f L n)) fun n ↦ by
    simp only [normalizedTwistedCubicalChainComplex, ChainComplex.of_d, ← ModuleCat.ofHom_comp,
      map_boundary]

/-- The components of the chain map induced by a continuous map. -/
@[simp]
theorem normalizedTwistedCubicalChainComplexMap_f (f : C(X, Y))
    (L : LocalCoefficientSystem.{u, v, w} R Y) (n : ℕ) :
    (normalizedTwistedCubicalChainComplexMap f L).f n = ModuleCat.ofHom (map f L n) := by
  unfold normalizedTwistedCubicalChainComplexMap
  rfl

/-- The identity of a local system induces the identity chain map. -/
@[simp]
theorem normalizedTwistedCubicalChainComplexCoefficientMap_id
    (L : LocalCoefficientSystem.{u, v, w} R X) :
    normalizedTwistedCubicalChainComplexCoefficientMap (𝟙 L) = 𝟙 _ := by
  ext n : 1
  simp only [normalizedTwistedCubicalChainComplexCoefficientMap_f, coefficientMap_id,
    HomologicalComplex.id_f]
  rfl

/-- A composite of morphisms of local systems induces the composite chain map. -/
theorem normalizedTwistedCubicalChainComplexCoefficientMap_comp
    {L K J : LocalCoefficientSystem.{u, v, w} R X} (η : L ⟶ K) (θ : K ⟶ J) :
    normalizedTwistedCubicalChainComplexCoefficientMap (η ≫ θ) =
      normalizedTwistedCubicalChainComplexCoefficientMap η ≫
        normalizedTwistedCubicalChainComplexCoefficientMap θ := by
  ext n : 1
  simp only [normalizedTwistedCubicalChainComplexCoefficientMap_f, HomologicalComplex.comp_f,
    coefficientMap_comp, ModuleCat.ofHom_comp]
  rfl

/-- The identity map induces on the normalized cubical chain complex the chain map coming from
the identification of a system with its pullback along the identity. -/
@[simp]
theorem normalizedTwistedCubicalChainComplexMap_id (L : LocalCoefficientSystem.{u, v, w} R X) :
    normalizedTwistedCubicalChainComplexMap (ContinuousMap.id X) L =
      normalizedTwistedCubicalChainComplexCoefficientMap ((pullbackIdIso X).hom.app L) := by
  ext n : 1
  simp only [normalizedTwistedCubicalChainComplexMap_f,
    normalizedTwistedCubicalChainComplexCoefficientMap_f,
    NormalizedTwistedCubicalChain.map_id]
  rfl

/-- A composite of continuous maps induces on normalized cubical chain complexes the composite of
the two induced chain maps, after the identification of the pullback along the composite with
the iterated pullback. -/
theorem normalizedTwistedCubicalChainComplexMap_comp (f : C(X, Y)) (g : C(Y, Z))
    (L : LocalCoefficientSystem.{u, v, w} R Z) :
    normalizedTwistedCubicalChainComplexMap (g.comp f) L =
      normalizedTwistedCubicalChainComplexCoefficientMap ((pullbackCompIso f g).hom.app L) ≫
        normalizedTwistedCubicalChainComplexMap f ((pullback g).obj L) ≫
          normalizedTwistedCubicalChainComplexMap g L := by
  ext n : 1
  simp only [normalizedTwistedCubicalChainComplexMap_f,
    normalizedTwistedCubicalChainComplexCoefficientMap_f,
    HomologicalComplex.comp_f, NormalizedTwistedCubicalChain.map_comp, ModuleCat.ofHom_comp]
  rfl

/-- The chain map induced by a continuous map is natural in the coefficient system. -/
theorem normalizedTwistedCubicalChainComplexMap_naturality (f : C(X, Y))
    {L K : LocalCoefficientSystem.{u, v, w} R Y} (η : L ⟶ K) :
    normalizedTwistedCubicalChainComplexMap f L ≫
        normalizedTwistedCubicalChainComplexCoefficientMap η =
      normalizedTwistedCubicalChainComplexCoefficientMap ((pullback f).map η) ≫
        normalizedTwistedCubicalChainComplexMap f K := by
  ext n : 1
  simp only [normalizedTwistedCubicalChainComplexMap_f,
    normalizedTwistedCubicalChainComplexCoefficientMap_f,
    HomologicalComplex.comp_f]
  exact congrArg ModuleCat.ofHom (NormalizedTwistedCubicalChain.coefficientMap_map η n)

end ChainComplex

end LocalCoefficientSystem

end TauCeti
