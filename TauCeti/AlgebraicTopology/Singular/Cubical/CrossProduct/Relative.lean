/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.AlgebraicTopology.Singular.Cubical.CrossProduct.Chains
public import TauCeti.AlgebraicTopology.Singular.Cubical.Relative
import Mathlib.LinearAlgebra.Quotient.Bilinear

/-!
# The relative cubical cross product

The cubical cross product descends to pairs:
`Cₚ(X, A) × Cq(Y, B) → Cₚ₊q(X × Y, A × Y ∪ X × B)`.
It is bilinear, natural under maps of pairs, and satisfies the signed Leibniz rule,
including when either factor has degree zero. In particular, the product of relative
cycles is a relative cycle. This is the chain operation used to take products of
fundamental chains relative to the boundary of a product of manifolds.

The support lemmas on normalized chains allow any target subspace containing the
appropriate product subspace. No closedness or separation assumptions are needed.

## References

* W. S. Massey, *Singular Homology Theory*, GTM 70, Springer, 1980, Chapter VII.
-/

public noncomputable section

namespace TauCeti

variable {X Y Z W : Type*} [TopologicalSpace X] [TopologicalSpace Y]
  [TopologicalSpace Z] [TopologicalSpace W] (R : Type*) [CommRing R]

namespace NormalizedCubicalChain

/-- Crossing a chain supported in `A` with any chain gives a chain supported in any
subspace containing `A × Y`. -/
theorem crossProduct_left_mem_supportedIn {A : Set X} {C : Set (X × Y)}
    (hC : A ×ˢ Set.univ ⊆ C) {p q : ℕ} {a : NormalizedCubicalChain X R p}
    (ha : a ∈ supportedIn R A p) (b : NormalizedCubicalChain Y R q) :
    crossProduct X Y R p q a b ∈ supportedIn R C (p + q) := by
  rw [supportedIn_def] at ha
  obtain ⟨a, rfl⟩ := ha
  let f : C(A × Y, C) := ⟨fun x ↦ ⟨(x.1.val, x.2), hC ⟨x.1.property, Set.mem_univ _⟩⟩,
    (continuous_subtype_val.comp continuous_fst).prodMk continuous_snd |>.subtype_mk _⟩
  rw [supportedIn_def]
  refine ⟨map R f (p + q) (crossProduct A Y R p q a b), ?_⟩
  have hf : (ContinuousMap.subtypeVal C).comp f =
      (ContinuousMap.subtypeVal A).prodMap (ContinuousMap.id Y) :=
    ContinuousMap.ext fun _ ↦ rfl
  rw [← LinearMap.comp_apply, ← map_comp, hf, map_crossProduct, map_id, LinearMap.id_apply]

/-- Crossing any chain with a chain supported in `B` gives a chain supported in any
subspace containing `X × B`. -/
theorem crossProduct_right_mem_supportedIn {B : Set Y} {C : Set (X × Y)}
    (hC : Set.univ ×ˢ B ⊆ C) {p q : ℕ} (a : NormalizedCubicalChain X R p)
    {b : NormalizedCubicalChain Y R q} (hb : b ∈ supportedIn R B q) :
    crossProduct X Y R p q a b ∈ supportedIn R C (p + q) := by
  rw [supportedIn_def] at hb
  obtain ⟨b, rfl⟩ := hb
  let f : C(X × B, C) := ⟨fun x ↦ ⟨(x.1, x.2.val), hC ⟨Set.mem_univ _, x.2.property⟩⟩,
    continuous_fst.prodMk (continuous_subtype_val.comp continuous_snd) |>.subtype_mk _⟩
  rw [supportedIn_def]
  refine ⟨map R f (p + q) (crossProduct X B R p q a b), ?_⟩
  have hf : (ContinuousMap.subtypeVal C).comp f =
      (ContinuousMap.id X).prodMap (ContinuousMap.subtypeVal B) :=
    ContinuousMap.ext fun _ ↦ rfl
  rw [← LinearMap.comp_apply, ← map_comp, hf, map_crossProduct, map_id, LinearMap.id_apply]

end NormalizedCubicalChain

namespace RelativeCubicalChain

variable (X Y) (A : Set X) (B : Set Y)

/-- The cross product of relative cubical chains, with target relative to the union
`A × Y ∪ X × B`. -/
def crossProduct (p q : ℕ) :
    RelativeCubicalChain X A R p →ₗ[R] RelativeCubicalChain Y B R q →ₗ[R]
      RelativeCubicalChain (X × Y) (A ×ˢ Set.univ ∪ Set.univ ×ˢ B) R (p + q) :=
  (LinearMap.compr₂ (NormalizedCubicalChain.crossProduct X Y R p q)
    (NormalizedCubicalChain.supportedIn R (A ×ˢ Set.univ ∪ Set.univ ×ˢ B) (p + q)).mkQ).liftQ₂
      (NormalizedCubicalChain.supportedIn R A p)
      (NormalizedCubicalChain.supportedIn R B q)
      (fun a ha ↦ LinearMap.mem_ker.2 (LinearMap.ext fun b ↦ by
        simpa using (Submodule.Quotient.mk_eq_zero _).2
          (NormalizedCubicalChain.crossProduct_left_mem_supportedIn R
            Set.subset_union_left ha b)))
      (fun b hb ↦ LinearMap.mem_ker.2 (LinearMap.ext fun a ↦ by
        simpa using (Submodule.Quotient.mk_eq_zero _).2
          (NormalizedCubicalChain.crossProduct_right_mem_supportedIn R
            Set.subset_union_right a hb)))

variable {X Y A B}

/-- The product of two relative classes is the class of their normalized cross product. -/
@[simp]
theorem crossProduct_mk {p q : ℕ} (a : NormalizedCubicalChain X R p)
    (b : NormalizedCubicalChain Y R q) :
    crossProduct X Y R A B p q (Submodule.Quotient.mk a) (Submodule.Quotient.mk b) =
      Submodule.Quotient.mk (NormalizedCubicalChain.crossProduct X Y R p q a b) := by
  simp [crossProduct]

/-- The relative cross product is natural under maps of pairs. -/
theorem map_crossProduct {A' : Set Z} {B' : Set W} (f : C(X, Z)) (g : C(Y, W))
    (hf : Set.MapsTo f A A') (hg : Set.MapsTo g B B') {p q : ℕ}
    (a : RelativeCubicalChain X A R p) (b : RelativeCubicalChain Y B R q) :
    map R (f.prodMap g) (by
          rintro ⟨x, y⟩ hx
          simpa only [ContinuousMap.prodMap_apply, Prod.map_apply] using
            ((hf.prodMap (Set.mapsTo_univ g Set.univ)).union_union
              ((Set.mapsTo_univ f Set.univ).prodMap hg)) hx) (p + q)
        (crossProduct X Y R A B p q a b) =
      crossProduct Z W R A' B' p q (map R f hf p a) (map R g hg q b) := by
  induction a using Submodule.Quotient.induction_on with
  | H a =>
    induction b using Submodule.Quotient.induction_on with
    | H b =>
      simp only [crossProduct_mk, map_mk, NormalizedCubicalChain.map_crossProduct]

/-- The signed Leibniz rule for relative chains in positive degrees. -/
theorem boundary_crossProduct {p q : ℕ} (a : RelativeCubicalChain X A R (p + 1))
    (b : RelativeCubicalChain Y B R (q + 1)) :
    boundary (X × Y) R (A ×ˢ Set.univ ∪ Set.univ ×ˢ B) (p + q + 1)
        (cast (X × Y) R _ (by omega : (p + 1) + (q + 1) = (p + q + 1) + 1)
          (crossProduct X Y R A B (p + 1) (q + 1) a b)) =
      crossProduct X Y R A B p (q + 1) (boundary X R A p a) b +
        (-1 : R) ^ (p + 1) • cast (X × Y) R _
          (by omega : (p + 1) + q = p + q + 1)
          (crossProduct X Y R A B (p + 1) q a (boundary Y R B q b)) := by
  induction a using Submodule.Quotient.induction_on with
  | H a =>
    induction b using Submodule.Quotient.induction_on with
    | H b => simp [NormalizedCubicalChain.boundary_crossProduct]

/-- The Leibniz rule when the right factor has degree zero. -/
theorem boundary_crossProduct_zero_right {p : ℕ} (a : RelativeCubicalChain X A R (p + 1))
    (b : RelativeCubicalChain Y B R 0) :
    boundary (X × Y) R (A ×ˢ Set.univ ∪ Set.univ ×ˢ B) p
        (crossProduct X Y R A B (p + 1) 0 a b) =
      crossProduct X Y R A B p 0 (boundary X R A p a) b := by
  induction a using Submodule.Quotient.induction_on with
  | H a =>
    induction b using Submodule.Quotient.induction_on with
    | H b => simp only [crossProduct_mk, boundary_mk,
        NormalizedCubicalChain.boundary_crossProduct_zero_right]

/-- The Leibniz rule when the left factor has degree zero. -/
theorem boundary_crossProduct_zero_left {q : ℕ} (a : RelativeCubicalChain X A R 0)
    (b : RelativeCubicalChain Y B R (q + 1)) :
    boundary (X × Y) R (A ×ˢ Set.univ ∪ Set.univ ×ˢ B) q
        (cast (X × Y) R _ (by omega : 0 + (q + 1) = q + 1)
          (crossProduct X Y R A B 0 (q + 1) a b)) =
      cast (X × Y) R _ (by omega : 0 + q = q)
        (crossProduct X Y R A B 0 q a (boundary Y R B q b)) := by
  induction a using Submodule.Quotient.induction_on with
  | H a =>
    induction b using Submodule.Quotient.induction_on with
    | H b => simp [NormalizedCubicalChain.boundary_crossProduct_zero_left]

end RelativeCubicalChain

end TauCeti
