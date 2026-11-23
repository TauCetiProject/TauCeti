/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import Mathlib.AlgebraicTopology.SimplicialObject.Basic
public import TauCeti.AlgebraicTopology.FatRealization
public import TauCeti.Topology.Compactness.Lindelof
import TauCeti.AlgebraicTopology.SimplexCategory.Basic

/-!
# Geometric realization of a simplicial space

For a simplicial space `X : SimplicialObject TopCat`, its thin *geometric realization*
`X.geometricRealization` (classically `|X|`) is the functor tensor product
`TauCeti.functorTensor SimplexCategory.toTop X`: the quotient of `Σ n : ℕ, X _⦋n⦌ × Δⁿ` by all
simplicial identifications `(X(f) x, t) ∼ (x, f_* t)` along morphisms `f : ⦋m⦌ ⟶ ⦋n⦌` in
`SimplexCategory`, with the quotient topology. Collapsing degeneracies yields the canonical
reindexing quotient comparison map `X.fatToGeometricRealization` from the fat realization of `X`.

This file specializes `TauCeti.functorTensor` to `SimplexCategory.toTop` with `ℕ`-indexed
characteristic maps (`geometricRealization.ι`), `ℕ`-indexed `ι`-evaluation `simp` lemmas
(`geometricRealization.lift_ι`, `geometricRealization.desc_ι`, `geometricRealization.map_ι`,
`geometricRealization.augment_ι`, `geometricRealization.homotopy_apply_ι`), `LindelofSpace` and
`UCompactlyGeneratedSpace` instances, and the fat-to-thin quotient comparison
(`fatToGeometricRealization`). Functoriality (`TauCeti.functorTensor.map`,
`TauCeti.functorTensorFunctor`), universal property (`TauCeti.functorTensor.desc`), augmentations
(`TauCeti.functorTensor.augment`), `[0, 1]`-homotopies (`TauCeti.functorTensor.homotopy`), and
open/closed restriction (`TauCeti.functorTensor.isOpenEmbedding_map`) are provided directly by
`TauCeti.functorTensor`. Unconditional injectivity and closed embeddings are proved via normal forms
in `TauCeti.AlgebraicTopology.SimplicialObject.GeometricRealization.Skeleton`.

## References

* G. Segal, *Classifying spaces and spectral sequences*, Publ. Math. IHÉS **34** (1968), 105–112.
* G. Segal, *Categories and cohomology theories*, Topology **13** (1974), 293–312, Appendix A.
* J. P. May, *The Geometry of Iterated Loop Spaces*, LNM **271**, Springer, 1972, §11.
* J. Ebert and O. Randal-Williams, *Semi-simplicial spaces*, Algebraic & Geometric Topology **19**
  (2019), 2099–2150, §1.2.
-/

public noncomputable section

open CategoryTheory Opposite Set Simplicial Topology

universe v u

namespace CategoryTheory.SimplicialObject

open SimplexCategory (toTop)

variable (X : SimplicialObject TopCat.{u})

/-- The thin geometric realization `|X|` of a simplicial space `X`: the functor tensor product
`TauCeti.functorTensor SimplexCategory.toTop X`. -/
abbrev geometricRealization : TopCat.{u} :=
  TauCeti.functorTensor toTop X

namespace geometricRealization

/-- The characteristic map `X _⦋n⦌ × Δⁿ → |X|` in degree `n`. -/
def ι (n : ℕ) : C(X _⦋n⦌ × toTop.{u}.obj ⦋n⦌, X.geometricRealization) :=
  TauCeti.functorTensor.ι toTop X ⦋n⦌

/-- `geometricRealization.ι X n` is the `⦋n⦌`-characteristic map of `functorTensor toTop X`. -/
theorem ι_eq (n : ℕ) : ι X n = TauCeti.functorTensor.ι toTop X ⦋n⦌ := (rfl)

@[simp] theorem ι_map {m n : ℕ} (f : ⦋m⦌ ⟶ ⦋n⦌) (x : X _⦋n⦌) (t : toTop.{u}.obj ⦋m⦌) :
    ι X m (X.map f.op x, t) = ι X n (x, toTop.map f t) :=
  TauCeti.functorTensor.ι_map toTop X f x t

theorem ι_jointly_surjective (p : X.geometricRealization) : ∃ n x t, ι X n (x, t) = p := by
  obtain ⟨⟨n⟩, x, t, rfl⟩ := TauCeti.functorTensor.ι_jointly_surjective toTop X p
  exact ⟨n, x, t, rfl⟩

theorem isQuotientMap_sigma :
    IsQuotientMap fun p : Σ n : ℕ, X _⦋n⦌ × toTop.{u}.obj ⦋n⦌ ↦ ι X p.1 p.2 :=
  have he : (fun p : Σ n : ℕ, X _⦋n⦌ × toTop.{u}.obj ⦋n⦌ ↦ ι X p.1 p.2) ∘
      (fun q : Σ d : SimplexCategory, X.obj (op d) × toTop.{u}.obj d ↦ ⟨q.1.len, q.2⟩) =
      fun q ↦ TauCeti.functorTensor.ι toTop X q.1 q.2 :=
    funext fun ⟨⟨_⟩, _⟩ ↦ rfl
  IsQuotientMap.of_comp
    (continuous_sigma fun d ↦
      continuous_sigmaMk (σ := fun n : ℕ ↦ X _⦋n⦌ × toTop.{u}.obj ⦋n⦌) (i := d.len))
    (continuous_sigma fun n ↦ (ι X n).continuous)
    (he.symm ▸ TauCeti.functorTensor.isQuotientMap_sigma toTop X)

theorem isOpen_iff {s : Set X.geometricRealization} : IsOpen s ↔ ∀ n, IsOpen (ι X n ⁻¹' s) :=
  TauCeti.functorTensor.isOpen_iff.trans ⟨fun h n ↦ h ⦋n⦌, fun h ⟨n⟩ ↦ h n⟩

theorem isClosed_iff {s : Set X.geometricRealization} : IsClosed s ↔ ∀ n, IsClosed (ι X n ⁻¹' s) :=
  TauCeti.functorTensor.isClosed_iff.trans ⟨fun h n ↦ h ⦋n⦌, fun h ⟨n⟩ ↦ h n⟩

theorem continuous_iff {Z : Type*} [TopologicalSpace Z] {g : X.geometricRealization → Z} :
    Continuous g ↔ ∀ n, Continuous (g ∘ ι X n) :=
  TauCeti.functorTensor.continuous_iff.trans ⟨fun h n ↦ h ⦋n⦌, fun h ⟨n⟩ ↦ h n⟩

/-- Two functions out of `|X|` agree once they agree on every degree. -/
theorem fun_ext {Z : Sort*} {g h : X.geometricRealization → Z}
    (H : ∀ n x t, g (ι X n (x, t)) = h (ι X n (x, t))) : g = h :=
  TauCeti.functorTensor.fun_ext fun ⟨n⟩ x t ↦ H n x t

/-- Two continuous maps out of `|X|` agree once they agree on every degree. -/
@[ext] theorem continuousMap_ext {Z : Type*} [TopologicalSpace Z]
    {g h : C(X.geometricRealization, Z)}
    (H : ∀ n x t, g (ι X n (x, t)) = h (ι X n (x, t))) : g = h :=
  ContinuousMap.coe_injective (fun_ext X H)

/-- Two morphisms out of `|X|` agree once they agree on every degree. -/
@[ext] theorem hom_ext {Z : TopCat.{u}} {g h : X.geometricRealization ⟶ Z}
    (H : ∀ n x t, g (ι X n (x, t)) = h (ι X n (x, t))) : g = h :=
  TopCat.hom_ext (continuousMap_ext X H)

instance [h : ∀ n : ℕ, LindelofSpace (X _⦋n⦌ × toTop.{u}.obj ⦋n⦌)] :
    LindelofSpace X.geometricRealization :=
  have : ∀ d : SimplexCategory, LindelofSpace (X.obj (op d) × toTop.{u}.obj d) := fun ⟨n⟩ ↦ h n
  TauCeti.functorTensor.instLindelofSpace toTop X

/-- If every level `X _⦋n⦌` is Lindelöf, then `X.geometricRealization` is Lindelöf. -/
instance (priority := 90) instLindelofSpace_of_levels [hX : ∀ n : ℕ, LindelofSpace (X _⦋n⦌)] :
    LindelofSpace X.geometricRealization :=
  have (n : ℕ) : LindelofSpace (X _⦋n⦌ × toTop.{u}.obj ⦋n⦌) :=
    have := hX n
    inferInstance
  inferInstance

instance [h : ∀ n : ℕ, UCompactlyGeneratedSpace.{v} (X _⦋n⦌ × toTop.{u}.obj ⦋n⦌)] :
    UCompactlyGeneratedSpace.{v} X.geometricRealization :=
  have : ∀ d : SimplexCategory, UCompactlyGeneratedSpace.{v} (X.obj (op d) × toTop.{u}.obj d) :=
    fun ⟨n⟩ ↦ h n
  TauCeti.functorTensor.instUCompactlyGeneratedSpace toTop X

section FunctorTensorSimp

variable {X}

@[simp] theorem lift_ι {Z : Sort*} (g : ∀ d : SimplexCategory, X.obj (op d) × toTop.{u}.obj d → Z)
    (hg : ∀ ⦃c d : SimplexCategory⦄ (f : c ⟶ d) (x : X.obj (op d)) (t : toTop.{u}.obj c),
      g c (X.map f.op x, t) = g d (x, toTop.map f t))
    (n : ℕ) (p : X _⦋n⦌ × toTop.{u}.obj ⦋n⦌) :
    TauCeti.functorTensor.lift g hg (ι X n p) = g ⦋n⦌ p :=
  TauCeti.functorTensor.lift_ι g hg ⦋n⦌ p

@[simp] theorem desc_ι {Z : Type*} [TopologicalSpace Z]
    (g : ∀ d : SimplexCategory, C(X.obj (op d) × toTop.{u}.obj d, Z))
    (hg : ∀ ⦃c d : SimplexCategory⦄ (f : c ⟶ d) (x : X.obj (op d)) (t : toTop.{u}.obj c),
      g c (X.map f.op x, t) = g d (x, toTop.map f t))
    (n : ℕ) (p : X _⦋n⦌ × toTop.{u}.obj ⦋n⦌) :
    TauCeti.functorTensor.desc g hg (ι X n p) = g ⦋n⦌ p :=
  TauCeti.functorTensor.desc_ι g hg ⦋n⦌ p

@[simp] theorem map_ι {Y : SimplicialObject TopCat.{u}} (φ : X ⟶ Y) (n : ℕ) (x : X _⦋n⦌)
    (t : toTop.{u}.obj ⦋n⦌) :
    TauCeti.functorTensor.map toTop φ (ι X n (x, t)) = ι Y n (φ.app (op ⦋n⦌) x, t) :=
  TauCeti.functorTensor.map_ι toTop φ ⦋n⦌ x t

@[simp] theorem augment_ι {Z : TopCat.{u}} (ε : X ⟶ (Functor.const _).obj Z) (n : ℕ) (x : X _⦋n⦌)
    (t : toTop.{u}.obj ⦋n⦌) :
    TauCeti.functorTensor.augment toTop ε (ι X n (x, t)) = ε.app (op ⦋n⦌) x :=
  TauCeti.functorTensor.augment_ι toTop ε ⦋n⦌ x t

@[simp] theorem homotopy_apply_ι {Y : SimplicialObject TopCat.{u}} (φ : unitInterval → (X ⟶ Y))
    (hφ : ∀ d : SimplexCategory,
      Continuous fun p : unitInterval × X.obj (op d) ↦ (φ p.fst).app (op d) p.snd)
    (s : unitInterval) (n : ℕ) (x : X _⦋n⦌) (t : toTop.{u}.obj ⦋n⦌) :
    TauCeti.functorTensor.homotopy toTop φ hφ (s, ι X n (x, t)) =
      ι Y n ((φ s).app (op ⦋n⦌) x, t) :=
  TauCeti.functorTensor.homotopy_apply_ι toTop φ hφ s ⦋n⦌ x t

end FunctorTensorSimp

end geometricRealization

open SemiSimplexCategory (toSimplexCategory)

/-- The canonical quotient comparison map `‖X‖ ⟶ |X|` from the fat realization of the underlying
semi-simplicial space to the thin geometric realization, collapsing degenerate simplices. -/
def fatToGeometricRealization :
    TauCeti.fatRealization (toSimplexCategory.op ⋙ X) ⟶ X.geometricRealization :=
  TauCeti.functorTensor.reindex toSimplexCategory toTop X

/-- `X.fatToGeometricRealization` is the reindexing morphism along
`SemiSimplexCategory.toSimplexCategory`. -/
theorem fatToGeometricRealization_eq :
    X.fatToGeometricRealization = TauCeti.functorTensor.reindex toSimplexCategory toTop X := (rfl)

@[simp↓] theorem fatToGeometricRealization_ι (m : SemiSimplexCategory)
    (x : (toSimplexCategory.op ⋙ X).obj (op m)) (t : SemiSimplexCategory.toTop.{u}.obj m) :
    X.fatToGeometricRealization
        (TauCeti.functorTensor.ι SemiSimplexCategory.toTop (toSimplexCategory.op ⋙ X) m (x, t)) =
      geometricRealization.ι X (toSimplexCategory.obj m).len (x, t) :=
  TauCeti.functorTensor.reindex_ι toSimplexCategory toTop X m x t

/-- The comparison map `‖X‖ ⟶ |X|` is a quotient map: `|X|` is a topological quotient of `‖X‖`. -/
theorem isQuotientMap_fatToGeometricRealization : IsQuotientMap X.fatToGeometricRealization :=
  TauCeti.functorTensor.isQuotientMap_reindex toSimplexCategory toTop X fun ⟨n⟩ ↦ ⟨.mk n, rfl⟩

/-- The comparison map `‖X‖ ⟶ |X|` is surjective. -/
theorem fatToGeometricRealization_surjective : Function.Surjective X.fatToGeometricRealization :=
  (isQuotientMap_fatToGeometricRealization X).surjective

/-- The comparison map `‖X‖ ⟶ |X|` is natural in the simplicial space `X`. -/
@[reassoc (attr := simp)] theorem fatRealization_map_comp_fatToGeometricRealization
    {X Y : SimplicialObject TopCat.{u}} (φ : X ⟶ Y) :
    TauCeti.functorTensor.map SemiSimplexCategory.toTop
        (Functor.whiskerLeft toSimplexCategory.op φ) ≫
      Y.fatToGeometricRealization =
        X.fatToGeometricRealization ≫ TauCeti.functorTensor.map toTop φ :=
  TauCeti.functorTensor.map_comp_reindex toSimplexCategory toTop φ

end CategoryTheory.SimplicialObject
