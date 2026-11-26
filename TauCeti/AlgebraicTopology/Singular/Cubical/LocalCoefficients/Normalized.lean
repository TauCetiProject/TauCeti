/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

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
augmentation all descend to the normalized chains; the chain complex they form is in
`TauCeti.AlgebraicTopology.Singular.Cubical.LocalCoefficients.ChainComplex`.

## Main definitions

* `TauCeti.LocalCoefficientSystem.TwistedCubicalChain.degenerate L n`: the degenerate chains.
* `TauCeti.LocalCoefficientSystem.NormalizedTwistedCubicalChain L n`: the normalized cubical
  chains.
* `TauCeti.LocalCoefficientSystem.NormalizedTwistedCubicalChain.boundary`, `.coefficientMap`,
  `.map`, `.augment`: the induced boundary, functoriality and augmentation.

## Main results

* `TauCeti.LocalCoefficientSystem.TwistedCubicalChain.boundary_ofCube_mem_degenerate`,
  `TauCeti.LocalCoefficientSystem.TwistedCubicalChain.degenerate_le_comap_boundary`: the
  degenerate chains form a subcomplex.
* `TauCeti.LocalCoefficientSystem.NormalizedTwistedCubicalChain.boundary_ofCube`: the boundary
  of a cube, and `TauCeti.LocalCoefficientSystem.NormalizedTwistedCubicalChain.boundary_boundary`:
  `∂ ∘ ∂ = 0`.
* `TauCeti.LocalCoefficientSystem.NormalizedTwistedCubicalChain.augment_boundary`: `ε ∘ ∂ = 0`.
* `TauCeti.LocalCoefficientSystem.NormalizedTwistedCubicalChain.map_id`,
  `TauCeti.LocalCoefficientSystem.NormalizedTwistedCubicalChain.map_comp`: functoriality.
* `TauCeti.LocalCoefficientSystem.TwistedCubicalChain.mem_degenerate_iff`: a chain is degenerate
  exactly when its components at the nondegenerate cubes vanish.
* `TauCeti.LocalCoefficientSystem.NormalizedTwistedCubicalChain.map_injective`: an injective
  continuous map, such as the inclusion of a subspace, induces an injective map of normalized
  chains, since a cube composed with an injective map is degenerate exactly when the cube is.

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

universe u v₁ v₂ v₃ w

namespace TauCeti

namespace LocalCoefficientSystem

open SingularCube
open ContinuousMap (pathClass pathClass_self pathClass_comp_pathClass)

variable {R : Type u} [Ring R] {X : TopCat.{v₁}} {Y : TopCat.{v₂}} {Z : TopCat.{v₃}}

namespace TwistedCubicalChain

section Degenerate

variable (L : LocalCoefficientSystem.{u, v₁, w} R X)

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
theorem degenerate_le_comap_coefficientMap {K : LocalCoefficientSystem.{u, v₁, w} R X}
    (η : L ⟶ K) (n : ℕ) : degenerate L n ≤ (degenerate K n).comap (coefficientMap η n) :=
  degenerate_le fun c hc a ↦ by
    rw [Submodule.mem_comap, coefficientMap_ofCube]
    exact ofCube_mem_degenerate hc _

/-- A continuous map preserves degenerate chains. -/
theorem degenerate_le_comap_map (f : C(X, Y)) (L : LocalCoefficientSystem.{u, v₂, w} R Y)
    (n : ℕ) : degenerate ((pullback f).obj L) n ≤ (degenerate L n).comap (map f L n) :=
  degenerate_le fun c hc a ↦ by
    rw [Submodule.mem_comap, map_ofCube]
    exact ofCube_mem_degenerate (hc.comp f) _

open scoped Classical in
/-- The restriction of a chain to the degenerate cubes is a degenerate chain. -/
private theorem filter_isDegenerate_mem_degenerate {n : ℕ} (y : L.TwistedCubicalChain n) :
    (DFinsupp.filter IsDegenerate y : L.TwistedCubicalChain n) ∈ degenerate L n := by
  induction y using induction_on with
  | zero => simp [DFinsupp.filter_zero]
  | ofCube c a =>
    -- `DirectSum.of` is `DFinsupp.single`, so filtering a single cube keeps it or kills it.
    by_cases hc : IsDegenerate c
    · have h : (DFinsupp.filter IsDegenerate (ofCube L c a) : L.TwistedCubicalChain n) =
          ofCube L c a := by
        rw [ofCube_eq_lof, DirectSum.lof_eq_of]
        exact DFinsupp.filter_single_pos _ _ hc
      rw [h]
      exact ofCube_mem_degenerate hc a
    · have h : (DFinsupp.filter IsDegenerate (ofCube L c a) : L.TwistedCubicalChain n) = 0 := by
        rw [ofCube_eq_lof, DirectSum.lof_eq_of]
        exact DFinsupp.filter_single_neg _ _ hc
      rw [h]
      exact Submodule.zero_mem _
  | add y z hy hz =>
    rw [DFinsupp.filter_add]
    exact Submodule.add_mem _ hy hz

/-- A chain is degenerate exactly when its components at the nondegenerate cubes vanish. -/
theorem mem_degenerate_iff {n : ℕ} (x : L.TwistedCubicalChain n) :
    x ∈ degenerate L n ↔ ∀ c, ¬IsDegenerate c → x c = 0 := by
  classical
  constructor
  · -- The chains vanishing at the nondegenerate cubes form a submodule containing every
    -- degenerate cube.
    let p : Submodule R (L.TwistedCubicalChain n) :=
      { carrier := {x | ∀ c, ¬IsDegenerate c → x c = 0}
        add_mem' := fun hx hy c hc ↦ by rw [DirectSum.add_apply, hx c hc, hy c hc, add_zero]
        zero_mem' := fun c _ ↦ DirectSum.zero_apply c
        smul_mem' := fun r x hx c hc ↦ by
          rw [DirectSum.smul_apply, hx c hc, smul_zero] }
    refine fun hx ↦ degenerate_le (p := p) (fun c hc a c' hc' ↦ ofCube_apply_of_ne ?_ a) hx
    rintro rfl
    exact hc' hc
  · -- Such a chain is its restriction to the degenerate cubes.
    intro hx
    have hxf : (DFinsupp.filter IsDegenerate x : L.TwistedCubicalChain n) = x :=
      DirectSum.ext fun c ↦ by
        by_cases hc : IsDegenerate c
        · exact DFinsupp.filter_apply_pos _ hc
        · rw [DFinsupp.filter_apply_neg _ hc, hx c hc]
    rw [← hxf]
    exact filter_isDegenerate_mem_degenerate x

/-- Along an injective map, a chain is degenerate exactly when its image is. -/
theorem map_mem_degenerate_iff_of_injective {f : C(X, Y)} (hf : Function.Injective f)
    {L : LocalCoefficientSystem.{u, v₂, w} R Y} {n : ℕ}
    (x : ((pullback f).obj L).TwistedCubicalChain n) :
    map f L n x ∈ degenerate L n ↔ x ∈ degenerate ((pullback f).obj L) n := by
  refine ⟨fun hx ↦ ?_, fun hx ↦ degenerate_le_comap_map f L n hx⟩
  rw [mem_degenerate_iff] at hx ⊢
  intro c hc
  rw [← map_apply_comp_of_injective hf]
  exact hx _ ((isDegenerate_comp_iff_of_injective f hf c).not.2 hc)

end Degenerate

end TwistedCubicalChain

/-- The **normalized cubical `n`-chains with coefficients in a local system** `L`: the cubical
chains with coefficients in `L` modulo the degenerate ones. -/
abbrev NormalizedTwistedCubicalChain (L : LocalCoefficientSystem.{u, v₁, w} R X) (n : ℕ) :
    Type (max v₁ w) :=
  L.TwistedCubicalChain n ⧸ TwistedCubicalChain.degenerate L n

namespace NormalizedTwistedCubicalChain


section Basic

variable (L : LocalCoefficientSystem.{u, v₁, w} R X)

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

/-- The classes of equal cubes agree on heterogeneously equal coefficients. -/
theorem ofCube_congr {n : ℕ} {c c' : SingularCube X n} (h : c = c')
    {a : L.obj (FundamentalGroupoid.mk (c 0))} {a' : L.obj (FundamentalGroupoid.mk (c' 0))}
    (ha : a ≍ a') : ofCube L c a = ofCube L c' a' := by
  subst h
  rw [eq_of_heq ha]

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

variable (L : LocalCoefficientSystem.{u, v₁, w} R X)

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

/-- The boundary of the class of a cube is the alternating sum of the classes of its faces, with
the coefficient transported along the path classes inside the cube to the origins of the faces. -/
@[simp]
theorem boundary_ofCube {n : ℕ} (c : SingularCube X (n + 1))
    (a : L.obj (FundamentalGroupoid.mk (c 0))) :
    boundary L n (ofCube L c a) =
      ∑ i : Fin (n + 1), ((-1 : ℤ) ^ (i : ℕ)) •
        (ofCube L (c.comp (face i 0 (ContinuousMap.id _)))
            (L.map (pathClass c 0 (face i 0 (ContinuousMap.id _) 0)) a) -
          ofCube L (c.comp (face i 1 (ContinuousMap.id _)))
            (L.map (pathClass c 0 (face i 1 (ContinuousMap.id _) 0)) a)) := by
  rw [ofCube_apply, boundary_mk, TwistedCubicalChain.boundary_ofCube]
  simp only [TwistedCubicalChain.ofSubcube_apply, ofCube_apply, ← Submodule.mkQ_apply, map_sum,
    map_zsmul, map_sub]

variable (L) in
/-- The boundary of a boundary vanishes. -/
theorem boundary_boundary (n : ℕ) : boundary L n ∘ₗ boundary L (n + 1) = 0 := by
  rw [boundary, boundary, ← Submodule.mapQ_comp]
  simp only [TwistedCubicalChain.boundary_boundary, Submodule.mapQ_zero]

end Boundary

section CoefficientMap

variable {L K J : LocalCoefficientSystem.{u, v₁, w} R X}

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

variable (f : C(X, Y)) (L : LocalCoefficientSystem.{u, v₂, w} R Y)

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
theorem coefficientMap_map {K : LocalCoefficientSystem.{u, v₂, w} R Y} (η : L ⟶ K) (n : ℕ) :
    coefficientMap η n ∘ₗ map f L n = map f K n ∘ₗ coefficientMap ((pullback f).map η) n := by
  rw [coefficientMap, coefficientMap, map, map, ← Submodule.mapQ_comp, ← Submodule.mapQ_comp]
  simp only [TwistedCubicalChain.coefficientMap_map]

/-- The identity map induces on normalized chains the map coming from the identification of a
system with its pullback along the identity. -/
@[simp]
theorem map_id (L : LocalCoefficientSystem.{u, v₁, w} R X) (n : ℕ) :
    map (ContinuousMap.id X) L n = coefficientMap ((pullbackIdIso X).hom.app L) n := by
  rw [map, coefficientMap]
  simp only [TwistedCubicalChain.map_id]
  rfl

/-- A composite of continuous maps induces on normalized chains the composite of the two induced
maps, after the identification of the pullback along the composite with the iterated
pullback. -/
theorem map_comp (g : C(Y, Z)) (L : LocalCoefficientSystem.{u, v₃, w} R Z) (n : ℕ) :
    map (g.comp f) L n = map g L n ∘ₗ map f ((pullback g).obj L) n ∘ₗ
      coefficientMap ((pullbackCompIso f g).hom.app L) n := by
  refine LinearMap.ext fun x ↦ Submodule.Quotient.induction_on _ x fun x ↦ ?_
  simp only [LinearMap.comp_apply, map_mk, coefficientMap_mk, TwistedCubicalChain.map_comp]

/-- Normalization preserves injectivity of a map of spaces: an injective continuous map induces an
injective map of normalized chains. No embedding hypothesis is needed. -/
theorem map_injective (hf : Function.Injective f) (n : ℕ) : Function.Injective (map f L n) := by
  rw [← LinearMap.ker_eq_bot, map, Submodule.ker_mapQ]
  have hcomap : (TwistedCubicalChain.degenerate L n).comap (TwistedCubicalChain.map f L n) =
      TwistedCubicalChain.degenerate ((pullback f).obj L) n := by
    ext x
    exact TwistedCubicalChain.map_mem_degenerate_iff_of_injective hf x
  rw [hcomap, Submodule.mkQ_map_self]

end Map

section Augment

variable {L : LocalCoefficientSystem.{u, v₁, w} R X}

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
theorem augment_coefficientMap {K : LocalCoefficientSystem.{u, v₁, w} R X} (η : L ⟶ K)
    (s : Cocone K) :
    augment s ∘ₗ coefficientMap η 0 = augment ((Cocone.precompose η).obj s) :=
  hom_ext fun c ↦ LinearMap.ext fun a ↦ by simp

/-- The augmentation is natural in the space. -/
theorem augment_map (f : C(X, Y)) {L : LocalCoefficientSystem.{u, v₂, w} R Y} (s : Cocone L) :
    augment s ∘ₗ map f L 0 = augment (s.whisker (FundamentalGroupoid.map f)) :=
  hom_ext fun c ↦ LinearMap.ext fun a ↦ (congrArg (augment s) (map_ofCube c a)).trans
    ((augment_ofCube (L := L) s (f.comp c) a).trans
      (augment_ofCube (s.whisker (FundamentalGroupoid.map f)) c a).symm)

end Augment

end NormalizedTwistedCubicalChain

end LocalCoefficientSystem

end TauCeti
