/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.Geometry.Manifold.Morse.Boundary.DegreeOneHomotopy

/-!
# The mod-two digon homotopy of a family of continuations

Let `f₀` and `f₁` be Morse functions on a compact boundaryless manifold `M`, with Morse–Smale
pseudo-gradients `X₀` and `X₁` adapted to them. Two continuations from `f₀` to `f₁` with the same
ends, along fields `V 0` and `V 1` on `M × ℝ`, give mod-two continuation maps `F⁰` and `F¹`
(`TauCeti.morseContinuationMap`). When the two continuations are homotopic with fixed ends, they are
joined by a family of fields `V λ` on `M × ℝ`, for `λ ∈ [0, 1]`; for instance the continuation
fields of a homotopy of paths `f_t^λ` with fixed endpoint germs. This one-parameter family of
continuations is the *digon* with vertices `f₀` and `f₁` and edges `V 0` and `V 1`. The statements
below use no relation between the fields `V λ` and the pseudo-gradients, so they take the family
`V : ℝ → (fields on M × ℝ)` as arbitrary data, of which only the parameters `λ ∈ [0, 1]` are read.

**The digon homotopy.** A *digon trajectory* from `p` to `q` is a pair `(λ, γ)` of a parameter
`λ ∈ [0, 1]` and a trajectory `γ` of `V λ` from `(p, 0)` to `(q, 1)`. For a generic family these
form a space of dimension `ind p - ind q + 1`: the dimension of the continuation trajectories of a
single field, plus one for the parameter. They are recorded by the parameter and the point of `γ` on
the middle level `t = 1 / 2` (`TauCeti.morseDigonSlice`). They are rigid when
`ind q = ind p + 1`: such trajectories, of continuation index `-1`, appear only at isolated
parameters. The homotopy `K = TauCeti.morseDegreeOneMap f₀ hf₁ (morseDigonSlice V)`, of degree
`+1`, counts them modulo two. As for the continuation map, the definitions take no hypothesis on
`V`; they are the trajectory counts only when the slices are finite, which is expected for
admissible families under the parametrized transversality condition, and is not proved here.

**The ends of the one-dimensional digon trajectory spaces.** When `ind p = ind q`, the digon
trajectories from `p` to `q` are expected to form a one-dimensional space with four kinds of ends:

* breaking at the source (`TauCeti.morseSourceBrokenDegreeOneSet` of the digon slices): a
  trajectory of `X₀` from `p` to a critical point `p'` of index `ind p - 1`, followed by a digon
  trajectory from `p'` to `q`;
* breaking at the target (`TauCeti.morseTargetBrokenDegreeOneSet` of the digon slices): a digon
  trajectory from `p` to a critical point `q'` of index `ind p + 1`, followed by a trajectory of
  `X₁` from `q'` to `q`;
* the edge `λ = 0`: a continuation trajectory of `V 0` from `(p, 0)` to `(q, 1)`;
* the edge `λ = 1`: a continuation trajectory of `V 1` from `(p, 0)` to `(q, 1)`.

When the slices are finite, these four sets count the `q`-coefficients of `K ∘ ∂₀`, `∂₁ ∘ K`, `F⁰`
and `F¹` applied to `p`. So the digon identity `∂₁ ∘ K + K ∘ ∂₀ = F⁰ + F¹` holds exactly when,
between any two critical points of equal index, the four kinds of ends are evenly many in total
(`TauCeti.morseBoundary_comp_morseDegreeOneMap_morseDigonSlice_add_eq_iff`). This is the algebraic
half of the independence of the continuation map from the choice of path within its homotopy class;
the geometric half, that these four sets are the ends of compact one-dimensional manifolds with
boundary, needs the compactification and gluing of the parametrized continuation trajectory spaces
and is not proved here. For a family of continuation fields with uniform end windows, the digon
trajectories are described through the transition maps of the slab in
`TauCeti.Geometry.Manifold.Morse.Boundary.Continuation.Digon`, which restates the criterion for
the intersections of the unstable manifolds of `X₀` with the preimages of the stable manifolds of
`X₁` under a one-parameter family of diffeomorphisms of `M`.

**The chain homotopy.** When `F⁰` is a chain map and the digon identity holds, `F¹` is a chain
map as well (`LinearMap.comp_eq_comp_of_comp_add_comp_eq_add`), and the graded homotopy
(`TauCeti.morseDegreeOneMapAt`) is a chain homotopy from the continuation morphism of `V 0` to that
of `V 1` (`TauCeti.morseDigonHomotopy`). By `Homotopy.homologyMap_eq`, the two continuations then
induce the same map on mod-two Morse homology. Together with the triangle homotopy
(`TauCeti.morseTriangleHomotopy`) this is what makes a reverse path an inverse up to homotopy: the
composite with the reverse continuation is homotopic to the constant path, whose continuation map
is the identity.

**Product families.** The homotopy of a family of product fields `(X x, Y λ t)` on `M × ℝ`, for a
Morse–Smale pseudo-gradient `X` adapted to `f`, vanishes
(`TauCeti.IsAdaptedPseudoGradient.IsMorseSmale.morseDegreeOneMap_morseDigonSlice_prodVectorField`):
their trajectories project to trajectories of `X`, which lower the index. For the constant family of
constant continuation fields, whose continuation maps are the identity, the digon identity then
reads `0 = id + id`, which holds over `ZMod 2`
(`morseBoundary_comp_morseDegreeOneMap_morseDigonSlice_constantContinuationField`, in the
namespace `TauCeti.IsAdaptedPseudoGradient.IsMorseSmale`).

## Main declarations

* `TauCeti.morseDigonSlice`: the parameters and middle-level points of the digon trajectories from
  `p` to `q`.
* `TauCeti.morseBoundary_comp_morseDegreeOneMap_morseDigonSlice_add_eq_iff`: the digon identity
  holds exactly when the ends of the digon trajectory spaces are evenly many.
* `TauCeti.morseDigonHomotopy`: the chain homotopy between the continuation morphisms of the two
  edges.

## References

* M. Hutchings, *Lecture notes on Morse homology (with an eye towards Floer theory and
  pseudoholomorphic curves)*, 2002, §4.2 (homotopic paths of Morse data give chain
  homotopic continuation maps, by counting index `-1` trajectories in the family).
* M. Audin and M. Damian, *Morse Theory and Floer Homology*, Springer Universitext, 2014,
  Chapter 6 (invariance of Morse homology by continuation).
-/

public section

open CategoryTheory Filter Set Topology
open scoped ContDiff Manifold

namespace TauCeti

variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
  {M : Type*} [TopologicalSpace M] [ChartedSpace E M]

section Definitions

variable {V : ℝ → (z : M × ℝ) → TangentSpace (𝓘(ℝ, E).prod 𝓘(ℝ)) z}

/-- The digon trajectories of a family `V` of vector fields on `M × ℝ` from `p` to `q`, recorded by
their parameter and their point on the middle level: the pairs `(λ, x)` with `λ ∈ [0, 1]` and `x`
on the middle level `t = 1 / 2` of a trajectory of `V λ` from `(p, 0)` to `(q, 1)`. -/
def morseDigonSlice (V : ℝ → (z : M × ℝ) → TangentSpace (𝓘(ℝ, E).prod 𝓘(ℝ)) z) (p q : M) :
    Set (ℝ × M) :=
  {y | y.1 ∈ Icc 0 1 ∧ y.2 ∈ morseContinuationSlice (V y.1) p q}

/-- Membership in the slice of the digon trajectories. -/
@[simp]
theorem mem_morseDigonSlice {p q : M} {y : ℝ × M} :
    y ∈ morseDigonSlice V p q ↔ y.1 ∈ Icc 0 1 ∧ y.2 ∈ morseContinuationSlice (V y.1) p q :=
  Iff.rfl

end Definitions

variable [FiniteDimensional ℝ E] [IsManifold 𝓘(ℝ, E) ∞ M] [CompactSpace M] [T2Space M]
  {f₀ f₁ : M → ℝ} {X₀ X₁ : (x : M) → TangentSpace 𝓘(ℝ, E) x}
  {V : ℝ → (z : M × ℝ) → TangentSpace (𝓘(ℝ, E).prod 𝓘(ℝ)) z}
  {hX₀ : IsAdaptedPseudoGradient f₀ X₀} {hX₁ : IsAdaptedPseudoGradient f₁ X₁}
  (h₀ : hX₀.IsMorseSmale) (hf₀ : IsMorse 𝓘(ℝ, E) f₀)
  (h₁ : hX₁.IsMorseSmale) (hf₁ : IsMorse 𝓘(ℝ, E) f₁)

include h₀ hf₀ h₁ in
/-- **The digon identity holds exactly when the ends of the digon trajectory spaces come in
pairs.** When the digon slices between critical points whose indices differ by one are finite, the
mod-two digon homotopy `K` of the family `V` satisfies `∂₁ ∘ K + K ∘ ∂₀ = F⁰ + F¹`, for the
continuation maps `F⁰` and `F¹` along `V 0` and `V 1`, exactly when, between any critical point `p`
of `f₀` and any critical point `q` of `f₁` of the same index, the digon trajectories broken at the
source and at the target, together with the continuation trajectories of `V 0` and of `V 1` on the
two edges, are evenly many in total. -/
theorem morseBoundary_comp_morseDegreeOneMap_morseDigonSlice_add_eq_iff
    (hV : ∀ (p : criticalPoints 𝓘(ℝ, E) f₀) (q : criticalPoints 𝓘(ℝ, E) f₁),
      manifoldMorseIndex 𝓘(ℝ, E) f₁ q = manifoldMorseIndex 𝓘(ℝ, E) f₀ p + 1 →
        (morseDigonSlice V p q).Finite) :
    h₁.morseBoundary hf₁ ∘ₗ morseDegreeOneMap f₀ hf₁ (morseDigonSlice V) +
        morseDegreeOneMap f₀ hf₁ (morseDigonSlice V) ∘ₗ h₀.morseBoundary hf₀ =
      morseContinuationMap f₀ hf₁ (V 0) + morseContinuationMap f₀ hf₁ (V 1) ↔
      ∀ (p : criticalPoints 𝓘(ℝ, E) f₀) (q : criticalPoints 𝓘(ℝ, E) f₁),
        manifoldMorseIndex 𝓘(ℝ, E) f₀ p = manifoldMorseIndex 𝓘(ℝ, E) f₁ q →
          Even ((morseSourceBrokenDegreeOneSet f₁ (morseDigonSlice V) hX₀ p q).ncard +
            (morseTargetBrokenDegreeOneSet f₀ (morseDigonSlice V) hX₁ p q).ncard +
              (morseContinuationSlice (V 0) p q).ncard +
                (morseContinuationSlice (V 1) p q).ncard) := by
  -- The two edges count the further ends.
  rw [morseBoundary_comp_morseDegreeOneMap_add_eq_iff h₀ hf₀ h₁ hf₁ hV (N := fun p q ↦
    (morseContinuationSlice (V 0) p q).ncard + (morseContinuationSlice (V 1) p q).ncard)
    fun p q ↦ ?_]
  · simp only [add_assoc]
  rw [LinearMap.add_apply, Finsupp.add_apply, morseContinuationMap_single_apply,
    morseContinuationMap_single_apply, one_mul, one_mul]
  split_ifs with hind
  · rw [morseContinuationCoeff_eq_ncard hind, morseContinuationCoeff_eq_ncard hind, Nat.cast_add]
  · rw [morseContinuationCoeff_eq_zero_of_manifoldMorseIndex_ne hind,
      morseContinuationCoeff_eq_zero_of_manifoldMorseIndex_ne hind, add_zero]

/-- **The digon homotopy.** When the continuation map `F⁰` along `V 0` commutes with the Morse
boundaries and the mod-two digon homotopy `K` of the family `V` satisfies
`∂₁ ∘ K + K ∘ ∂₀ = F⁰ + F¹`, the graded digon homotopy is a chain homotopy from the continuation
morphism of `V 0` to that of `V 1`. So the two continuations induce the same map on mod-two Morse
homology (`Homotopy.homologyMap_eq`). -/
noncomputable def morseDigonHomotopy
    (hcomm : h₁.morseBoundary hf₁ ∘ₗ morseContinuationMap f₀ hf₁ (V 0) =
      morseContinuationMap f₀ hf₁ (V 0) ∘ₗ h₀.morseBoundary hf₀)
    (hK : h₁.morseBoundary hf₁ ∘ₗ morseDegreeOneMap f₀ hf₁ (morseDigonSlice V) +
        morseDegreeOneMap f₀ hf₁ (morseDigonSlice V) ∘ₗ h₀.morseBoundary hf₀ =
      morseContinuationMap f₀ hf₁ (V 0) + morseContinuationMap f₀ hf₁ (V 1)) :
    Homotopy (morseContinuationHom h₀ hf₀ h₁ hf₁ hcomm)
      (morseContinuationHom h₀ hf₀ h₁ hf₁
        (LinearMap.comp_eq_comp_of_comp_add_comp_eq_add (h₀.morseBoundary_comp_morseBoundary hf₀)
          (h₁.morseBoundary_comp_morseBoundary hf₁) hcomm hK)) :=
  morseDegreeOneHomotopy h₀ hf₀ h₁ hf₁ _ (morseContinuationHom_f h₀ hf₀ h₁ hf₁ hcomm)
    (fun _ ↦ mapDomain_morseContinuationMapAt hf₁) hcomm hK

/-- The components of the digon homotopy are the graded digon homotopies. -/
@[simp]
theorem morseDigonHomotopy_hom
    (hcomm : h₁.morseBoundary hf₁ ∘ₗ morseContinuationMap f₀ hf₁ (V 0) =
      morseContinuationMap f₀ hf₁ (V 0) ∘ₗ h₀.morseBoundary hf₀)
    (hK : h₁.morseBoundary hf₁ ∘ₗ morseDegreeOneMap f₀ hf₁ (morseDigonSlice V) +
        morseDegreeOneMap f₀ hf₁ (morseDigonSlice V) ∘ₗ h₀.morseBoundary hf₀ =
      morseContinuationMap f₀ hf₁ (V 0) + morseContinuationMap f₀ hf₁ (V 1)) (i j : ℕ) :
    (morseDigonHomotopy h₀ hf₀ h₁ hf₁ hcomm hK).hom i j =
      ModuleCat.ofHom (morseDegreeOneMapAt f₀ hf₁ (morseDigonSlice V) i j) :=
  morseDegreeOneHomotopy_hom h₀ hf₀ h₁ hf₁ _ _ _ hcomm hK i j

/-! ### Product families -/

namespace IsAdaptedPseudoGradient.IsMorseSmale

variable {f : M → ℝ} {X : (x : M) → TangentSpace 𝓘(ℝ, E) x}
  {hX : IsAdaptedPseudoGradient f X} (h : hX.IsMorseSmale) (hf : IsMorse 𝓘(ℝ, E) f)

include h hf in
/-- **Product families have no digon trajectories raising the index.** Under the Morse–Smale
condition, for every family `Y` of fields on `ℝ`, the family of product fields `(X x, Y λ t)` on
`M × ℝ` has no digon trajectory from `p` to `q` when `ind p < ind q`: the space component of each
trajectory is a trajectory of `X` from `p` to `q`, which lowers the index. -/
theorem morseDigonSlice_prodVectorField_eq_empty
    (Y : ℝ → (t : ℝ) → TangentSpace 𝓘(ℝ) t) {p q : M}
    (hind : manifoldMorseIndex 𝓘(ℝ, E) f p < manifoldMorseIndex 𝓘(ℝ, E) f q) :
    morseDigonSlice (fun l ↦ Manifold.prodVectorField X (Y l)) p q = ∅ := by
  refine eq_empty_of_forall_notMem fun y hy ↦ ?_
  obtain ⟨γ, hγ, -, hp, hq⟩ := mem_morseContinuationSlice.1 hy.2
  exact (h.manifoldMorseIndex_le_of_isMIntegralCurve_prodVectorField hf hγ hp hq).not_gt hind

include h hf in
/-- **The digon homotopy of a product family vanishes.** Under the Morse–Smale condition, for every
family `Y` of fields on `ℝ`, the mod-two digon homotopy of the family of product fields
`(X x, Y λ t)` on `M × ℝ` is zero. -/
@[simp]
theorem morseDegreeOneMap_morseDigonSlice_prodVectorField
    (Y : ℝ → (t : ℝ) → TangentSpace 𝓘(ℝ) t) :
    morseDegreeOneMap f hf (morseDigonSlice fun l ↦ Manifold.prodVectorField X (Y l)) = 0 :=
  morseDegreeOneMap_eq_zero_of_slice_eq_empty hf fun _ _ hind ↦
    h.morseDigonSlice_prodVectorField_eq_empty hf Y (by omega)

include h in
/-- **The digon identity for the constant family of constant paths.** Under the Morse–Smale
condition, for `C > 0`, the constant family of constant continuation fields `(X x, C t (1 - t²))`
satisfies the digon identity `∂ ∘ K + K ∘ ∂ = F⁰ + F¹`: its digon homotopy `K` vanishes, as for
every product family, and both edges have the identity as continuation map, so the identity reads
`0 = id + id`, which holds over `ZMod 2`. -/
theorem morseBoundary_comp_morseDegreeOneMap_morseDigonSlice_constantContinuationField
    {C : ℝ} (hC : 0 < C) :
    h.morseBoundary hf ∘ₗ
        morseDegreeOneMap f hf (morseDigonSlice fun _ ↦ constantContinuationField X C) +
      morseDegreeOneMap f hf (morseDigonSlice fun _ ↦ constantContinuationField X C) ∘ₗ
        h.morseBoundary hf =
      morseContinuationMap f hf (constantContinuationField X C) +
        morseContinuationMap f hf (constantContinuationField X C) := by
  have hK : morseDegreeOneMap f hf (morseDigonSlice fun _ ↦ constantContinuationField X C) = 0 := by
    simp only [constantContinuationField_def]
    exact h.morseDegreeOneMap_morseDigonSlice_prodVectorField hf _
  rw [hK, h.morseContinuationMap_constantContinuationField hf hC, LinearMap.comp_zero,
    LinearMap.zero_comp, add_zero]
  refine LinearMap.ext fun c ↦ ?_
  rw [LinearMap.zero_apply, LinearMap.add_apply, LinearMap.id_apply, ZModModule.add_self]

end IsAdaptedPseudoGradient.IsMorseSmale

end TauCeti
