/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import Mathlib.Algebra.Category.ModuleCat.Basic
public import Mathlib.Algebra.Homology.HomologicalComplex
public import Mathlib.Algebra.Homology.ShortComplex.HomologicalComplex
public import Mathlib.Algebra.Homology.ShortComplex.ModuleCat
public import Mathlib.Topology.Category.TopCat.Basic
public import TauCeti.Algebra.Homology.ModuleCat.Basic
public import TauCeti.AlgebraicTopology.Singular.Cubical.Normalization

/-!
# The normalized cubical chain complex functor

The normalized cubical chains of a topological space, with their boundary, form a chain complex
of modules over the coefficient ring, and continuous maps induce chain maps.  This packages the
concrete normalized cubical chains of `TauCeti.AlgebraicTopology.Singular.Cubical.Normalized` as a
functor `TopCat ⥤ ChainComplex (ModuleCat R) ℕ`, the form in which they are compared with the
simplicial singular chain complex. The raw cubical chains, degenerate cubes included, likewise form
a functor, with the normalization quotient a natural chain map onto the normalized chains.

## Main definitions

* `TauCeti.normalizedCubicalChainComplex R`: the functor sending a space to its normalized cubical
  chain complex with coefficients in `R`.
* `TauCeti.rawCubicalChainComplex k`: the raw cubical chain complex functor.
* `TauCeti.rawCubicalChainComplexπ k`: the normalization quotient, a natural chain map to the
  normalized cubical chains.

## Main results

* `TauCeti.isZero_normalizedCubicalChainComplex_obj_of_isEmpty`: the normalized cubical chains of
  an empty space vanish.
* `TauCeti.NormalizedCubicalChain.exists_boundary_eq_of_isZero_homology`: if the normalized
  cubical homology vanishes in dimension `n + 1`, every `(n + 1)`-cycle is a boundary.
* `TauCeti.normalizedCubicalChainComplex_homologyπ_eq_iff`: two cycles have the same homology
  class exactly when the difference of their chains is a boundary.
-/

@[expose] public section

noncomputable section

open CategoryTheory

universe u r w

namespace TauCeti

section Normalized

variable (R : Type u) [Ring R]

/-- The **normalized cubical chain complex** of a topological space, with coefficients in `R`. -/
def normalizedCubicalChainComplexObj (X : TopCat.{u}) : ChainComplex (ModuleCat.{u} R) ℕ :=
  ChainComplex.of (fun n ↦ ModuleCat.of R (NormalizedCubicalChain X R n))
    (fun n ↦ ModuleCat.ofHom (NormalizedCubicalChain.boundary X R n))
    fun n ↦ by
      rw [← ModuleCat.ofHom_comp, NormalizedCubicalChain.boundary_boundary]
      rfl

/-- The **normalized cubical chain complex functor**, with coefficients in `R`. -/
def normalizedCubicalChainComplex : TopCat.{u} ⥤ ChainComplex (ModuleCat.{u} R) ℕ where
  obj X := normalizedCubicalChainComplexObj R X
  map f := ChainComplex.ofHom
    (fun n ↦ ModuleCat.ofHom (NormalizedCubicalChain.map R f.hom n)) fun n ↦ by
      simp only [normalizedCubicalChainComplexObj, ChainComplex.of_d,
        ← ModuleCat.ofHom_comp, NormalizedCubicalChain.map_boundary]
  map_id X := by
    ext n x
    simp [normalizedCubicalChainComplexObj]
  map_comp f g := by
    ext n x
    simp [normalizedCubicalChainComplexObj, NormalizedCubicalChain.map_comp]

variable {R}

@[simp]
theorem normalizedCubicalChainComplex_obj_X (X : TopCat.{u}) (n : ℕ) :
    ((normalizedCubicalChainComplex R).obj X).X n = ModuleCat.of R (NormalizedCubicalChain X R n) :=
  (rfl)

@[simp]
theorem normalizedCubicalChainComplex_obj_d_apply (X : TopCat.{u}) (n : ℕ)
    (x : NormalizedCubicalChain X R (n + 1)) :
    ((normalizedCubicalChainComplex R).obj X).d (n + 1) n x =
      NormalizedCubicalChain.boundary X R n x := by
  simp only [normalizedCubicalChainComplex, normalizedCubicalChainComplexObj, ChainComplex.of_d]
  rfl

/-- The concrete identification of a term of the normalized cubical chain complex with the
corresponding module of normalized cubical chains. -/
def normalizedCubicalChainComplexXEquiv (X : TopCat.{u}) (n : ℕ) :
    ((normalizedCubicalChainComplex R).obj X).X n ≃ₗ[R] NormalizedCubicalChain X R n :=
  LinearEquiv.refl R _

/-- The concrete identification of a chain-complex term acts as the identity on elements. -/
@[simp]
theorem normalizedCubicalChainComplexXEquiv_apply (X : TopCat.{u}) (n : ℕ)
    (g : ((normalizedCubicalChainComplex R).obj X).X n) :
    normalizedCubicalChainComplexXEquiv X n g = g :=
  rfl

/-- The inverse concrete identification acts as the identity on normalized cubical chains. -/
@[simp]
theorem normalizedCubicalChainComplexXEquiv_symm_apply (X : TopCat.{u}) (n : ℕ)
    (g : NormalizedCubicalChain X R n) :
    (normalizedCubicalChainComplexXEquiv X n).symm g = g :=
  rfl

/-- Under the concrete identification, the chain-complex differential is the cubical boundary. -/
theorem normalizedCubicalChainComplexXEquiv_d_apply (X : TopCat.{u}) (n : ℕ)
    (g : ((normalizedCubicalChainComplex R).obj X).X (n + 1)) :
    normalizedCubicalChainComplexXEquiv X n
        (((normalizedCubicalChainComplex R).obj X).d (n + 1) n g) =
      NormalizedCubicalChain.boundary X R n
        (normalizedCubicalChainComplexXEquiv X (n + 1) g) :=
  normalizedCubicalChainComplex_obj_d_apply X n g

/-- The boundary of a cycle of the normalized cubical chain complex vanishes, for every
reindexing of its degree `q` as `p + 1`. -/
theorem NormalizedCubicalChain.boundary_cast_iCycles_eq_zero {X : TopCat.{u}} {q : ℕ}
    (z : ((normalizedCubicalChainComplex R).obj X).cycles q) (p : ℕ) (hp : q = p + 1) :
    NormalizedCubicalChain.boundary X R p
      (NormalizedCubicalChain.cast R hp
        ((((normalizedCubicalChainComplex R).obj X).iCycles q).hom z)) = 0 := by
  subst hp
  exact (congrArg (NormalizedCubicalChain.boundary X R p)
    (NormalizedCubicalChain.cast_rfl R _)).trans
      ((normalizedCubicalChainComplex_obj_d_apply X p _).symm.trans
        (ConcreteCategory.congr_hom (((normalizedCubicalChainComplex R).obj X).iCycles_d _ _) z))

/-- In each degree, the map of normalized cubical chain complexes induced by a map of spaces is
the push-forward of normalized cubical chains. -/
theorem normalizedCubicalChainComplex_map_f {X Y : TopCat.{u}} (f : X ⟶ Y) (n : ℕ) :
    ((normalizedCubicalChainComplex R).map f).f n =
      ModuleCat.ofHom (NormalizedCubicalChain.map R f.hom n) :=
  (rfl)

@[simp]
theorem normalizedCubicalChainComplex_map_f_apply {X Y : TopCat.{u}} (f : X ⟶ Y) (n : ℕ)
    (x : NormalizedCubicalChain X R n) :
    ((normalizedCubicalChainComplex R).map f).f n x = NormalizedCubicalChain.map R f.hom n x :=
  (rfl)

/-- Under the concrete term identifications, a map of cubical complexes is the push-forward
of normalized chains. -/
theorem normalizedCubicalChainComplexXEquiv_map_f_apply {X Y : TopCat.{u}} (f : X ⟶ Y)
    (n : ℕ) (x : ((normalizedCubicalChainComplex R).obj X).X n) :
    normalizedCubicalChainComplexXEquiv Y n
        (((normalizedCubicalChainComplex R).map f).f n x) =
      NormalizedCubicalChain.map R f.hom n (normalizedCubicalChainComplexXEquiv X n x) :=
  (rfl)

/-- The terms of the normalized cubical chain complex are projective modules. -/
instance (X : TopCat.{u}) (n : ℕ) :
    Module.Projective R (((normalizedCubicalChainComplex R).obj X).X n) :=
  inferInstanceAs (Module.Projective R (NormalizedCubicalChain X R n))

/-- The normalized cubical chains of an empty space vanish, as there are no singular cubes in
it. -/
theorem isZero_normalizedCubicalChainComplex_obj_of_isEmpty (X : TopCat.{u}) [IsEmpty X] :
    Limits.IsZero ((normalizedCubicalChainComplex R).obj X) := by
  rw [Limits.IsZero.iff_id_eq_zero]
  ext n x
  have : IsEmpty (SingularCube X n) := ⟨fun c ↦ isEmptyElim (c fun _ ↦ 0)⟩
  have : Subsingleton (NormalizedCubicalChain X R n) :=
    (Submodule.Quotient.mk_surjective _).subsingleton
  exact this.elim _ _

/-- If the normalized cubical homology of `X` vanishes in dimension `n + 1`, every normalized
cubical `(n + 1)`-cycle of `X` is a boundary. -/
theorem NormalizedCubicalChain.exists_boundary_eq_of_isZero_homology {X : TopCat.{u}} {n : ℕ}
    (h : Limits.IsZero (((normalizedCubicalChainComplex R).obj X).homology (n + 1)))
    {c : NormalizedCubicalChain X R (n + 1)} (hc : NormalizedCubicalChain.boundary X R n c = 0) :
    ∃ c' : NormalizedCubicalChain X R (n + 2),
      NormalizedCubicalChain.boundary X R (n + 1) c' = c := by
  have hex := (((normalizedCubicalChainComplex R).obj X).exactAt_iff_isZero_homology (n + 1)).2 h
  rw [HomologicalComplex.exactAt_iff' _ (n + 2) (n + 1) n (by simp) (by simp),
    ShortComplex.moduleCat_exact_iff] at hex
  obtain ⟨c', hc'⟩ := hex c ((normalizedCubicalChainComplex_obj_d_apply X n c).trans hc)
  exact ⟨c', (normalizedCubicalChainComplex_obj_d_apply X (n + 1) c').symm.trans hc'⟩

/-- Two cycles of the normalized cubical chain complex have the same homology class exactly when
the difference of the chains they represent is a boundary. -/
theorem normalizedCubicalChainComplex_homologyπ_eq_iff {X : TopCat.{u}} (q : ℕ)
    (z z' : ((normalizedCubicalChainComplex R).obj X).cycles q) :
    ((normalizedCubicalChainComplex R).obj X).homologyπ q z =
        ((normalizedCubicalChainComplex R).obj X).homologyπ q z' ↔
      ∃ c : NormalizedCubicalChain X R (q + 1), NormalizedCubicalChain.boundary X R q c =
        normalizedCubicalChainComplexXEquiv X q
            (((normalizedCubicalChainComplex R).obj X).iCycles q z) -
          normalizedCubicalChainComplexXEquiv X q
            (((normalizedCubicalChainComplex R).obj X).iCycles q z') := by
  rw [HomologicalComplex.moduleCat_homologyπ_eq_iff _ (m := q + 1) (by simp)]
  constructor
  · rintro ⟨c, hc⟩
    exact ⟨normalizedCubicalChainComplexXEquiv _ _ c,
      (normalizedCubicalChainComplexXEquiv_d_apply _ q c).symm.trans (by rw [hc, map_sub])⟩
  · rintro ⟨c, hc⟩
    refine ⟨(normalizedCubicalChainComplexXEquiv _ _).symm c,
      (normalizedCubicalChainComplexXEquiv (R := R) _ q).injective ?_⟩
    exact (normalizedCubicalChainComplexXEquiv_d_apply _ q _).trans (hc.trans (map_sub _ _ _).symm)

end Normalized


/-- The native chain-complex object on original raw cubes with arbitrary module coefficients.
The coefficient ring universe is independent of the space and coefficient-module universes. -/
noncomputable def rawCubicalChainComplexObj {R : Type r} [Ring R]
    (X : TopCat.{w}) (M : ModuleCat.{max u w} R) : ChainComplex (ModuleCat.{max u w} R) ℕ :=
  ChainComplex.of (fun n ↦ ModuleCat.of R (SingularCube X n →₀ M))
    (fun n ↦ ModuleCat.ofHom (CubicalChain.boundary X R M n)) fun n ↦ by
      rw [← ModuleCat.ofHom_comp,
        CubicalChain.boundary_boundary]
      rfl


/-- A raw complex term is the original finitely supported coefficient module. -/
@[simp]
lemma rawCubicalChainComplexObj_X {R : Type r} [Ring R] (X : TopCat.{w})
    (M : ModuleCat.{max u w} R) (n : ℕ) :
    (rawCubicalChainComplexObj X M).X n = ModuleCat.of R (SingularCube X n →₀ M) := by
  rfl

/-- The native raw differential acts by the unique module-valued cubical boundary. -/
@[simp]
lemma rawCubicalChainComplexObj_d_apply {R : Type r} [Ring R] (X : TopCat.{w})
    (M : ModuleCat.{max u w} R) (n : ℕ) (c : SingularCube X (n + 1) →₀ M) :
    ((rawCubicalChainComplexObj X M).d (n + 1) n).hom c =
      CubicalChain.boundary X R M n c := by
  simp only [rawCubicalChainComplexObj, ChainComplex.of_d]
  rfl


/-! ### The raw cubical chain complex functor -/

section Raw

open Finsupp

variable (k : Type u) [Ring k]

/-- The **raw cubical chain complex functor** with coefficients in `k`: the formal combinations of
all singular cubes, degenerate ones included, with the cubical boundary. -/
def rawCubicalChainComplex : TopCat.{u} ⥤ ChainComplex (ModuleCat.{u} k) ℕ where
  obj X := rawCubicalChainComplexObj X (ModuleCat.of k k)
  map {X Y} f := ChainComplex.ofHom
    (fun _ ↦ ModuleCat.ofHom (lmapDomain (ModuleCat.of k k) k f.hom.comp)) fun n ↦
      ModuleCat.hom_ext <| LinearMap.ext fun x ↦
        (rawCubicalChainComplexObj_d_apply Y _ n _).trans
          ((LinearMap.congr_fun (CubicalChain.lmapDomain_comp_boundary k _ f.hom n) x).symm.trans
            (congrArg (lmapDomain (ModuleCat.of k k) k f.hom.comp)
              (rawCubicalChainComplexObj_d_apply X _ n x).symm))
  map_id _ := HomologicalComplex.hom_ext _ _ fun _ ↦
    ModuleCat.hom_ext (LinearMap.ext fun _ ↦ mapDomain_id)
  map_comp f g := HomologicalComplex.hom_ext _ _ fun _ ↦
    ModuleCat.hom_ext (LinearMap.ext fun x ↦
      mapDomain_comp (f := f.hom.comp) (g := g.hom.comp) (v := x))

variable {k}

/-- The raw cubical chain complex of a space is the native raw complex with coefficients in `k`. -/
theorem rawCubicalChainComplex_obj (X : TopCat.{u}) :
    (rawCubicalChainComplex k).obj X = rawCubicalChainComplexObj X (ModuleCat.of k k) :=
  (rfl)

/-- In each degree, the map of raw cubical chain complexes induced by a map of spaces is the
push-forward of raw cubical chains along composition with the map. -/
theorem rawCubicalChainComplex_map_f {X Y : TopCat.{u}} (f : X ⟶ Y) (n : ℕ) :
    ((rawCubicalChainComplex k).map f).f n =
      ModuleCat.ofHom (lmapDomain (ModuleCat.of k k) k f.hom.comp) :=
  (rfl)

/-- The map of raw cubical chains induced by a map of spaces acts by `Finsupp.mapDomain`. -/
@[simp]
theorem rawCubicalChainComplex_map_f_apply {X Y : TopCat.{u}} (f : X ⟶ Y) (n : ℕ)
    (x : SingularCube X n →₀ k) :
    ((rawCubicalChainComplex k).map f).f n x = mapDomain f.hom.comp x :=
  (rfl)

/-- A singular cube, as a raw cubical chain with coefficient one. -/
def rawCubicalChainOfCube {X : TopCat.{u}} {n : ℕ} (c : SingularCube X n) :
    ((rawCubicalChainComplex k).obj X).X n :=
  single c (1 : k)

theorem rawCubicalChainOfCube_def {X : TopCat.{u}} {n : ℕ} (c : SingularCube X n) :
    rawCubicalChainOfCube (k := k) c = single c 1 :=
  (rfl)

/-- Two linear maps out of the raw cubical `n`-chains agree if they agree on every cube. -/
@[ext]
theorem rawCubicalChainComplex_X_linearMap_ext {X : TopCat.{u}} {n : ℕ} {M : Type*}
    [AddCommGroup M] [Module k M] {f₁ f₂ : ((rawCubicalChainComplex k).obj X).X n →ₗ[k] M}
    (h : ∀ c : SingularCube X n, f₁ (rawCubicalChainOfCube c) = f₂ (rawCubicalChainOfCube c)) :
    f₁ = f₂ := by
  simp only [rawCubicalChainOfCube_def] at h
  exact lhom_ext' (φ := f₁) (ψ := f₂) fun c ↦ LinearMap.ext_ring (h c)

/-- A continuous map sends the raw chain of a cube `c` to that of `f ∘ c`. -/
@[simp]
theorem rawCubicalChainComplex_map_f_rawCubicalChainOfCube {X Y : TopCat.{u}} (f : X ⟶ Y) {n : ℕ}
    (c : SingularCube X n) :
    ((rawCubicalChainComplex k).map f).f n (rawCubicalChainOfCube c) =
      rawCubicalChainOfCube (f.hom.comp c) :=
  (rawCubicalChainComplex_map_f_apply f n _).trans mapDomain_single

/-- The boundary of the raw chain of a cube is the signed sum of the raw chains of its faces. -/
@[simp]
theorem rawCubicalChainComplex_d_rawCubicalChainOfCube {X : TopCat.{u}} {n : ℕ}
    (c : SingularCube X (n + 1)) :
    ((rawCubicalChainComplex k).obj X).d (n + 1) n (rawCubicalChainOfCube c) =
      ∑ i : Fin (n + 1), (-1 : k) ^ (i : ℕ) •
        (rawCubicalChainOfCube (SingularCube.face i 0 c) -
          rawCubicalChainOfCube (SingularCube.face i 1 c)) := by
  simp only [rawCubicalChainOfCube_def]
  refine (rawCubicalChainComplexObj_d_apply X (ModuleCat.of k k) n (single c (1 : k))).trans
    ((CubicalChain.boundary_single (M := ModuleCat.of k k) k c (1 : k)).trans
      (Finset.sum_congr rfl fun i _ ↦ ?_))
  rw [← Int.cast_smul_eq_zsmul k, Int.cast_pow, Int.cast_neg, Int.cast_one]
  -- The two sides differ only in the module structure: `ModuleCat.of k k` versus `k`.
  rfl

variable (k)

/-- The normalization quotient from the raw to the normalized cubical chains, as a natural chain
map. -/
def rawCubicalChainComplexπ : rawCubicalChainComplex k ⟶ normalizedCubicalChainComplex k where
  app X := ChainComplex.ofHom (fun n ↦ ModuleCat.ofHom (CubicalChain.degenerate X k n).mkQ)
    fun n ↦ ModuleCat.hom_ext <| LinearMap.ext fun x ↦
      (normalizedCubicalChainComplex_obj_d_apply X n _).trans
        ((NormalizedCubicalChain.boundary_mk k x).trans
          (congrArg Submodule.Quotient.mk (rawCubicalChainComplexObj_d_apply X _ n x).symm))
  naturality _ Y f := HomologicalComplex.hom_ext _ _ fun n ↦ ModuleCat.hom_ext <|
    rawCubicalChainComplex_X_linearMap_ext fun c ↦
      (congrArg (CubicalChain.degenerate Y k n).mkQ
        (rawCubicalChainComplex_map_f_rawCubicalChainOfCube f c)).trans
      ((congrArg Submodule.Quotient.mk (CubicalChain.map_single k f.hom c (1 : k))).symm.trans
        (NormalizedCubicalChain.map_mk k f.hom _).symm)

variable {k}

/-- The normalization quotient sends the raw chain of a cube to its normalized class. -/
@[simp]
theorem rawCubicalChainComplexπ_app_f_rawCubicalChainOfCube {X : TopCat.{u}} {n : ℕ}
    (c : SingularCube X n) :
    ((rawCubicalChainComplexπ k).app X).f n (rawCubicalChainOfCube c) =
      (normalizedCubicalChainComplexXEquiv X n).symm (NormalizedCubicalChain.ofCube X k c) :=
  (NormalizedCubicalChain.ofCube_def k c).symm

end Raw

end TauCeti
