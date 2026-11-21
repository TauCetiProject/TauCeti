/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import Mathlib.Analysis.Normed.Group.Submodule
public import Mathlib.Analysis.Normed.Operator.NormedSpace
public import TauCeti.Analysis.Calculus.Jet.HigherOrder
public import TauCeti.Analysis.Calculus.Jet.LinearCoordChange
public import TauCeti.Topology.Algebra.Module.Multilinear.Symmetrize

/-!
# Symmetric finite jets and their coordinate changes

Over `ℝ` or `ℂ`, the derivative tuple `(D⁰ s(x), D¹ s(x), …, Dʳ s(x))` of a `C^r` map consists of
symmetric multilinear maps, and every tuple of symmetric multilinear maps is the derivative tuple
of a polynomial. The symmetric tuples form a closed subspace `TauCeti.symmetricJets 𝕜 E F r` of
all tuples. With its norm it is the normed space `TauCeti.SymmetricJet 𝕜 E F r`, the fibre of the
bundle of `r`-jets of a vector bundle with fibre `F` over a manifold modelled on `E`. This type
synonym of the subspace carries only the norm topology, so that continuous linear maps between
spaces of symmetric jets carry their operator norm.

The coordinate change of jets `TauCeti.linearJetCoordChange` is defined on all tuples, but it
satisfies the identity law only on symmetric tuples, and it takes symmetric tuples to symmetric
tuples only where the coordinate maps are `C^r`. The symmetrization `TauCeti.jetSymmetrize`,
applied componentwise, takes all tuples to symmetric ones, and in characteristic zero it is a
continuous linear projection onto them. Composing with it gives `TauCeti.symmetricJetCoordChange`,
a continuous linear map between spaces of symmetric jets which is defined for all coordinate maps
and is as smooth in the base point as `linearJetCoordChange`. In characteristic zero it agrees
with `linearJetCoordChange` wherever the coordinate maps are `C^r` (analytic over fields other
than `ℝ` and `ℂ`), satisfies the identity law, and satisfies the cocycle law wherever the
coordinate maps are `C^r` (analytic over other fields). These are the transition maps of the jet
bundle.

## Main declarations

* `TauCeti.symmetricJets`: the closed subspace of symmetric `r`-jet tuples, and
  `TauCeti.SymmetricJet`: the corresponding normed space.
* `TauCeti.jetSymmetrize`: the componentwise symmetrization, in characteristic zero a continuous
  linear projection onto the symmetric jets (`TauCeti.jetSymmetrize_coeFn`).
* `TauCeti.iteratedFDeriv_mem_symmetricJets`: derivative tuples of `C^r` maps are symmetric.
* `TauCeti.symmetricJetCoordChange`: the coordinate change of symmetric `r`-jets, with
  `TauCeti.coeFn_symmetricJetCoordChange` comparing it with `TauCeti.linearJetCoordChange`.
* `TauCeti.symmetricJetCoordChange_id`, `TauCeti.symmetricJetCoordChange_comp`,
  `TauCeti.symmetricJetCoordChange_congr`: the identity, cocycle and germ laws.
* `TauCeti.coeFn_symmetricJetCoordChange_iteratedFDeriv`: it transforms the jet of a section into
  the jet of the transformed section.
* `TauCeti.SymmetricJet.truncate`: truncation of symmetric jets to lower order, which commutes
  with coordinate changes (`TauCeti.SymmetricJet.truncate_symmetricJetCoordChange`).
* `ContDiffOn.symmetricJetCoordChange`: smoothness in the base point.

## References

* I. Kolář, P. W. Michor and J. Slovák, *Natural Operations in Differential Geometry*,
  §§12.2–12.5, for jets of vector bundles and their coordinate transformations.
-/

public section

noncomputable section

open Equiv Filter Function
open scoped ContDiff Topology

variable {𝕜 E E' E'' F G H : Type*} [NontriviallyNormedField 𝕜]
  [NormedAddCommGroup E] [NormedSpace 𝕜 E]
  [NormedAddCommGroup E'] [NormedSpace 𝕜 E']
  [NormedAddCommGroup E''] [NormedSpace 𝕜 E'']
  [NormedAddCommGroup F] [NormedSpace 𝕜 F]
  [NormedAddCommGroup G] [NormedSpace 𝕜 G]
  [NormedAddCommGroup H] [NormedSpace 𝕜 H]

namespace TauCeti

/-! ### Symmetric jets -/

variable (𝕜 E F) in
/-- The **symmetric `r`-jets**: the tuples `(A₀, …, Aᵣ)` of continuous multilinear maps
`Aᵢ : E [×i]→L[𝕜] F` each of which is symmetric, that is, invariant under permutations of its
arguments. These are the derivative tuples of `C^r` maps over `ℝ` or `ℂ`. -/
def symmetricJets (r : ℕ) : Submodule 𝕜 ((i : Fin (r + 1)) → E [×i]→L[𝕜] F) where
  carrier := {A | ∀ (i : Fin (r + 1)) (v : Fin i → E) (σ : Perm (Fin i)), A i (v ∘ σ) = A i v}
  add_mem' hA hB i v σ := by simp [hA i v σ, hB i v σ]
  zero_mem' _ _ _ := rfl
  smul_mem' c A hA i v σ := by simp [hA i v σ]

/-- A tuple is a symmetric jet when each of its components is invariant under permutations of its
arguments. -/
theorem mem_symmetricJets {r : ℕ} {A : (i : Fin (r + 1)) → E [×i]→L[𝕜] F} :
    A ∈ symmetricJets 𝕜 E F r ↔
      ∀ (i : Fin (r + 1)) (v : Fin i → E) (σ : Perm (Fin i)), A i (v ∘ σ) = A i v :=
  Iff.rfl

/-- The symmetric jets form a closed subspace. -/
theorem isClosed_symmetricJets (r : ℕ) :
    IsClosed (symmetricJets 𝕜 E F r : Set ((i : Fin (r + 1)) → E [×i]→L[𝕜] F)) := by
  have : (symmetricJets 𝕜 E F r : Set ((i : Fin (r + 1)) → E [×i]→L[𝕜] F)) =
      ⋂ (i : Fin (r + 1)) (v : Fin i → E) (σ : Perm (Fin i)), {A | A i (v ∘ σ) = A i v} := by
    ext A
    simp [mem_symmetricJets]
  rw [this]
  refine isClosed_iInter fun i ↦ isClosed_iInter fun v ↦ isClosed_iInter fun σ ↦ isClosed_eq ?_ ?_
  · exact (ContinuousMultilinearMap.apply 𝕜 _ F (v ∘ σ)).continuous.comp (continuous_apply i)
  · exact (ContinuousMultilinearMap.apply 𝕜 _ F v).continuous.comp (continuous_apply i)

/-- Over `ℝ` or `ℂ`, the derivative tuple of a map which is `C^r` at `x` is a symmetric jet; over
other fields the same holds for analytic maps. -/
theorem iteratedFDeriv_mem_symmetricJets {r : ℕ} {n : ℕ∞ω} {s : E → F} {x : E}
    (hs : ContDiffAt 𝕜 n s x) (hn : minSmoothness 𝕜 r ≤ n) :
    (fun i : Fin (r + 1) ↦ iteratedFDeriv 𝕜 i s x) ∈ symmetricJets 𝕜 E F r := fun i v σ ↦
  hs.iteratedFDeriv_comp_perm_of_le
    ((minSmoothness_monotone (by exact_mod_cast i.is_le)).trans hn) v σ

/-! ### The normed space of symmetric jets -/

variable (𝕜 E F) in
/-- The **normed space of symmetric `r`-jets**, the fibre coordinates of the bundle of `r`-jets.
It is the subspace `TauCeti.symmetricJets 𝕜 E F r` with its norm. This type synonym carries only
the norm topology, so that continuous linear maps between spaces of symmetric jets carry their
operator norm. -/
@[expose] def SymmetricJet (r : ℕ) : Type _ :=
  symmetricJets 𝕜 E F r

namespace SymmetricJet

variable {r : ℕ}

instance : NormedAddCommGroup (SymmetricJet 𝕜 E F r) :=
  inferInstanceAs (NormedAddCommGroup (symmetricJets 𝕜 E F r))

instance : NormedSpace 𝕜 (SymmetricJet 𝕜 E F r) :=
  inferInstanceAs (NormedSpace 𝕜 (symmetricJets 𝕜 E F r))

instance [CompleteSpace F] : CompleteSpace (SymmetricJet 𝕜 E F r) :=
  (isClosed_symmetricJets (𝕜 := 𝕜) (E := E) (F := F) r).completeSpace_coe

/-- A symmetric jet is a tuple of continuous multilinear maps; `A i` is its component of
order `i`. -/
instance : CoeFun (SymmetricJet 𝕜 E F r) fun _ ↦ (i : Fin (r + 1)) → E [×i]→L[𝕜] F :=
  ⟨fun A ↦ (A : symmetricJets 𝕜 E F r).val⟩

/-- The symmetric jet with the given symmetric components. -/
def mk (A : (i : Fin (r + 1)) → E [×i]→L[𝕜] F) (hA : A ∈ symmetricJets 𝕜 E F r) :
    SymmetricJet 𝕜 E F r :=
  (⟨A, hA⟩ : symmetricJets 𝕜 E F r)

/-- The components of `SymmetricJet.mk A hA` are those of `A`. -/
@[simp]
theorem mk_apply (A : (i : Fin (r + 1)) → E [×i]→L[𝕜] F) (hA : A ∈ symmetricJets 𝕜 E F r) :
    ⇑(mk A hA) = A :=
  (rfl)

/-- The components of a symmetric jet form a symmetric tuple. -/
theorem coeFn_mem_symmetricJets (A : SymmetricJet 𝕜 E F r) : ⇑A ∈ symmetricJets 𝕜 E F r :=
  (A : symmetricJets 𝕜 E F r).property

/-- Each component of a symmetric jet is invariant under permutations of its arguments. -/
theorem apply_comp_perm (A : SymmetricJet 𝕜 E F r) (i : Fin (r + 1)) (v : Fin i → E)
    (σ : Perm (Fin i)) : A i (v ∘ σ) = A i v :=
  A.coeFn_mem_symmetricJets i v σ

/-- A symmetric jet is determined by its components. -/
theorem coeFn_injective : Function.Injective fun A : SymmetricJet 𝕜 E F r ↦ ⇑A :=
  fun _ _ h ↦ Subtype.ext h

/-- Two symmetric jets with the same components are equal. -/
@[ext]
theorem ext {A B : SymmetricJet 𝕜 E F r} (h : ∀ i, A i = B i) : A = B :=
  coeFn_injective (funext h)

/-- The components of a sum are the sums of the components. -/
@[simp]
theorem add_apply (A B : SymmetricJet 𝕜 E F r) (i : Fin (r + 1)) : (A + B) i = A i + B i :=
  (rfl)

/-- The components of the zero jet are zero. -/
@[simp]
theorem zero_apply (i : Fin (r + 1)) : (0 : SymmetricJet 𝕜 E F r) i = 0 :=
  (rfl)

/-- The components of a negation are the negations of the components. -/
@[simp]
theorem neg_apply (A : SymmetricJet 𝕜 E F r) (i : Fin (r + 1)) : (-A) i = -A i :=
  (rfl)

/-- The components of a difference are the differences of the components. -/
@[simp]
theorem sub_apply (A B : SymmetricJet 𝕜 E F r) (i : Fin (r + 1)) : (A - B) i = A i - B i :=
  (rfl)

/-- The components of a scalar multiple are the scalar multiples of the components. -/
@[simp]
theorem smul_apply (c : 𝕜) (A : SymmetricJet 𝕜 E F r) (i : Fin (r + 1)) :
    (c • A) i = c • A i :=
  (rfl)

variable (𝕜 E F r) in
/-- The inclusion of the symmetric jets into all tuples, as a continuous linear map. -/
@[expose] def subtypeL : SymmetricJet 𝕜 E F r →L[𝕜] (i : Fin (r + 1)) → E [×i]→L[𝕜] F :=
  (symmetricJets 𝕜 E F r).subtypeL

/-- The inclusion of the symmetric jets sends a jet to its components. -/
@[simp]
theorem subtypeL_apply (A : SymmetricJet 𝕜 E F r) : subtypeL 𝕜 E F r A = ⇑A :=
  (rfl)

end SymmetricJet

/-! ### Symmetrization of jets -/

variable (𝕜 E F) in
/-- The **symmetrization of jets**: the componentwise symmetrization
`ContinuousMultilinearMap.symmetrize`, a continuous linear map from all `r`-jet tuples to the
symmetric jets. In characteristic zero it is a projection onto the symmetric jets
(`TauCeti.jetSymmetrize_coeFn`). -/
def jetSymmetrize (r : ℕ) : ((i : Fin (r + 1)) → E [×i]→L[𝕜] F) →L[𝕜] SymmetricJet 𝕜 E F r :=
  (ContinuousLinearMap.pi fun i : Fin (r + 1) ↦
    (ContinuousMultilinearMap.symmetrize 𝕜 (Fin i) E F).comp
      (ContinuousLinearMap.proj (R := 𝕜) (φ := fun i : Fin (r + 1) ↦ E [×i]→L[𝕜] F) i)).codRestrict
    (symmetricJets 𝕜 E F r) fun A i v σ ↦
      ContinuousMultilinearMap.symmetrize_apply_comp_perm (A i) v σ

/-- The components of the symmetrization of a jet are the symmetrizations of its components. -/
@[simp]
theorem jetSymmetrize_apply {r : ℕ} (A : (i : Fin (r + 1)) → E [×i]→L[𝕜] F)
    (i : Fin (r + 1)) :
    jetSymmetrize 𝕜 E F r A i = ContinuousMultilinearMap.symmetrize 𝕜 (Fin i) E F (A i) :=
  (rfl)

/-- The symmetrization of a symmetric tuple has the same components. -/
theorem coeFn_jetSymmetrize_of_mem [CharZero 𝕜] {r : ℕ}
    {A : (i : Fin (r + 1)) → E [×i]→L[𝕜] F} (hA : A ∈ symmetricJets 𝕜 E F r) :
    ⇑(jetSymmetrize 𝕜 E F r A) = A := by
  funext i
  exact ContinuousMultilinearMap.symmetrize_eq_self (hA i)

/-- The symmetrization of a symmetric tuple is the corresponding symmetric jet. -/
theorem jetSymmetrize_of_mem [CharZero 𝕜] {r : ℕ} {A : (i : Fin (r + 1)) → E [×i]→L[𝕜] F}
    (hA : A ∈ symmetricJets 𝕜 E F r) : jetSymmetrize 𝕜 E F r A = SymmetricJet.mk A hA :=
  SymmetricJet.coeFn_injective (coeFn_jetSymmetrize_of_mem hA)

/-- **The symmetrization is a projection onto the symmetric jets** in characteristic zero. -/
@[simp]
theorem jetSymmetrize_coeFn [CharZero 𝕜] {r : ℕ} (A : SymmetricJet 𝕜 E F r) :
    jetSymmetrize 𝕜 E F r ⇑A = A :=
  SymmetricJet.coeFn_injective (coeFn_jetSymmetrize_of_mem A.coeFn_mem_symmetricJets)

/-- The symmetrization composed with the inclusion of the symmetric jets is the identity. -/
@[simp]
theorem jetSymmetrize_comp_subtypeL [CharZero 𝕜] (r : ℕ) :
    jetSymmetrize 𝕜 E F r ∘L SymmetricJet.subtypeL 𝕜 E F r = ContinuousLinearMap.id 𝕜 _ :=
  ContinuousLinearMap.ext jetSymmetrize_coeFn

/-! ### Coordinate changes of symmetric jets -/

/-- The **coordinate change of symmetric `r`-jets** under a change of base coordinates
`h : E' → E` and a base-dependent linear change of fibre coordinates `g : E' → F →L[𝕜] G`, at the
point `x : E'`: the coordinate change of jets `TauCeti.linearJetCoordChange` followed by the
symmetrization. In characteristic zero, where `h` and `g` are `C^r` (analytic over fields other
than `ℝ` and `ℂ`), the symmetrization does nothing (`TauCeti.coeFn_symmetricJetCoordChange`). -/
def symmetricJetCoordChange (r : ℕ) (h : E' → E) (g : E' → F →L[𝕜] G) (x : E') :
    SymmetricJet 𝕜 E F r →L[𝕜] SymmetricJet 𝕜 E' G r :=
  jetSymmetrize 𝕜 E' G r ∘L linearJetCoordChange r h g x ∘L SymmetricJet.subtypeL 𝕜 E F r

/-- Unfolding the coordinate change of symmetric jets. -/
theorem symmetricJetCoordChange_apply (r : ℕ) (h : E' → E) (g : E' → F →L[𝕜] G) (x : E')
    (A : SymmetricJet 𝕜 E F r) :
    symmetricJetCoordChange r h g x A = jetSymmetrize 𝕜 E' G r (linearJetCoordChange r h g x ⇑A) :=
  (rfl)

/-- Where the coordinate maps are `C^n` with `minSmoothness 𝕜 r ≤ n` (`C^r` over `ℝ` or `ℂ`,
analytic otherwise), the coordinate change of symmetric jets is the coordinate change of jets. -/
theorem coeFn_symmetricJetCoordChange [CharZero 𝕜] {r : ℕ} {n : ℕ∞ω} {h : E' → E}
    {g : E' → F →L[𝕜] G} {x : E'} (hh : ContDiffAt 𝕜 n h x) (hg : ContDiffAt 𝕜 n g x)
    (hn : minSmoothness 𝕜 r ≤ n) (A : SymmetricJet 𝕜 E F r) :
    ⇑(symmetricJetCoordChange r h g x A) = linearJetCoordChange r h g x ⇑A :=
  coeFn_jetSymmetrize_of_mem fun i v σ ↦ linearJetCoordChange_apply_comp_perm i hh hg
    ((minSmoothness_monotone (by exact_mod_cast i.is_le)).trans hn) _ v σ

/-- **The identity law** for coordinate changes of symmetric jets. -/
@[simp]
theorem symmetricJetCoordChange_id [CharZero 𝕜] (r : ℕ) (x : E) :
    symmetricJetCoordChange r id (fun _ ↦ ContinuousLinearMap.id 𝕜 F) x =
      ContinuousLinearMap.id 𝕜 (SymmetricJet 𝕜 E F r) := by
  ext1 A
  rw [symmetricJetCoordChange_apply, linearJetCoordChange_id x A.coeFn_mem_symmetricJets,
    jetSymmetrize_coeFn, ContinuousLinearMap.id_apply]

/-- **The cocycle law** for coordinate changes of symmetric jets. If `h₁` and `g₁` are `C^n` at
`h₂ x` with `minSmoothness 𝕜 r ≤ n` (`C^r` over `ℝ` or `ℂ`, analytic otherwise) and `h₂` and
`g₂` are `C^r` at `x`, then transforming a symmetric jet first by `(h₁, g₁)` at `h₂ x` and then by
`(h₂, g₂)` at `x` is transforming it by the composite coordinate change
`(h₁ ∘ h₂, z ↦ g₂ z ∘ g₁ (h₂ z))` at `x`. -/
theorem symmetricJetCoordChange_comp [CharZero 𝕜] {r : ℕ} {n : ℕ∞ω}
    {h₁ : E' → E} {g₁ : E' → F →L[𝕜] G} {h₂ : E'' → E'} {g₂ : E'' → G →L[𝕜] H} {x : E''}
    (hh₁ : ContDiffAt 𝕜 n h₁ (h₂ x)) (hg₁ : ContDiffAt 𝕜 n g₁ (h₂ x))
    (hn : minSmoothness 𝕜 r ≤ n) (hh₂ : ContDiffAt 𝕜 r h₂ x) (hg₂ : ContDiffAt 𝕜 r g₂ x) :
    symmetricJetCoordChange r h₂ g₂ x ∘L symmetricJetCoordChange r h₁ g₁ (h₂ x) =
      symmetricJetCoordChange r (h₁ ∘ h₂) (fun z ↦ (g₂ z).comp (g₁ (h₂ z))) x := by
  ext1 A
  rw [ContinuousLinearMap.comp_apply, symmetricJetCoordChange_apply r h₂,
    coeFn_symmetricJetCoordChange hh₁ hg₁ hn, linearJetCoordChange_comp hh₁ hg₁ hn hh₂ hg₂,
    symmetricJetCoordChange_apply]

/-- Coordinate changes of symmetric jets depend only on the germs of the coordinate maps. -/
theorem symmetricJetCoordChange_congr {r : ℕ} {h h' : E' → E} {g g' : E' → F →L[𝕜] G}
    {x : E'} (hh : h =ᶠ[𝓝 x] h') (hg : g =ᶠ[𝓝 x] g') :
    symmetricJetCoordChange r h g x = symmetricJetCoordChange r h' g' x := by
  rw [symmetricJetCoordChange, linearJetCoordChange_congr hh hg, symmetricJetCoordChange]

/-- **Coordinate changes of jets of sections.** If `h`, `g` and `s` are `C^n` at the relevant
points with `minSmoothness 𝕜 r ≤ n` (`C^r` over `ℝ` or `ℂ`, analytic otherwise), the coordinate
change of symmetric `r`-jets takes the `r`-jet of `s` at `h x` to the `r`-jet at `x` of the
transformed map `z ↦ g z (s (h z))`. -/
theorem coeFn_symmetricJetCoordChange_iteratedFDeriv [CharZero 𝕜] {r : ℕ} {n : ℕ∞ω}
    {h : E' → E} {g : E' → F →L[𝕜] G} {x : E'} {s : E → F} (hs : ContDiffAt 𝕜 n s (h x))
    (hh : ContDiffAt 𝕜 n h x) (hg : ContDiffAt 𝕜 n g x) (hn : minSmoothness 𝕜 r ≤ n) :
    ⇑(symmetricJetCoordChange r h g x
        (SymmetricJet.mk (fun i : Fin (r + 1) ↦ iteratedFDeriv 𝕜 i.val s (h x))
          (iteratedFDeriv_mem_symmetricJets hs hn))) =
      fun i : Fin (r + 1) ↦ iteratedFDeriv 𝕜 i.val (fun z ↦ g z (s (h z))) x := by
  rw [coeFn_symmetricJetCoordChange hh hg hn, SymmetricJet.mk_apply]
  exact linearJetCoordChange_iteratedFDeriv hs hn (hh.of_le (le_minSmoothness.trans hn))
    (hg.of_le (le_minSmoothness.trans hn))

/-! ### Truncation of symmetric jets -/

namespace SymmetricJet

variable (𝕜 E F) in
/-- The **truncation** of symmetric `r`-jets to order `r' ≤ r`, forgetting the components of
order greater than `r'`: the truncation `TauCeti.jetTruncate` of their components
(`TauCeti.SymmetricJet.coeFn_truncate`). -/
def truncate {r' r : ℕ} (hr : r' ≤ r) : SymmetricJet 𝕜 E F r →L[𝕜] SymmetricJet 𝕜 E F r' :=
  (ContinuousLinearMap.pi fun i : Fin (r' + 1) ↦
    (ContinuousLinearMap.proj (R := 𝕜) (φ := fun i : Fin (r + 1) ↦ E [×i]→L[𝕜] F)
      (i.castLE (Nat.add_le_add_right hr 1))).comp (subtypeL 𝕜 E F r)).codRestrict
    (symmetricJets 𝕜 E F r') fun A i v σ ↦
      A.apply_comp_perm (i.castLE (Nat.add_le_add_right hr 1)) v σ

/-- The components of a truncated jet are the truncation of its components. -/
@[simp]
theorem coeFn_truncate {r' r : ℕ} (hr : r' ≤ r) (A : SymmetricJet 𝕜 E F r) :
    ⇑(truncate 𝕜 E F hr A) = jetTruncate hr ⇑A :=
  funext fun i ↦ (jetTruncate_apply hr ⇑A i).symm

/-- Truncating to the same order is the identity. -/
@[simp]
theorem truncate_rfl (r : ℕ) : truncate 𝕜 E F (le_refl r) = ContinuousLinearMap.id 𝕜 _ := by
  ext1 A
  exact coeFn_injective ((coeFn_truncate _ A).trans (jetTruncate_refl r ⇑A))

/-- Truncations compose. -/
@[simp]
theorem truncate_comp_truncate {r'' r' r : ℕ} (hr' : r'' ≤ r') (hr : r' ≤ r) :
    truncate 𝕜 E F hr' ∘L truncate 𝕜 E F hr = truncate 𝕜 E F (hr'.trans hr) := by
  ext1 A
  refine coeFn_injective ?_
  simp only [ContinuousLinearMap.comp_apply, coeFn_truncate, jetTruncate_trans]

end SymmetricJet

/-- Truncation commutes with the symmetrization. -/
theorem SymmetricJet.truncate_jetSymmetrize {r' r : ℕ} (hr : r' ≤ r)
    (A : (i : Fin (r + 1)) → E [×i]→L[𝕜] F) :
    SymmetricJet.truncate 𝕜 E F hr (jetSymmetrize 𝕜 E F r A) =
      jetSymmetrize 𝕜 E F r' (jetTruncate hr A) := by
  ext1 i
  rw [SymmetricJet.coeFn_truncate, jetTruncate_apply, jetSymmetrize_apply,
    jetSymmetrize_apply, jetTruncate_apply]
  -- The symmetrizations are over `Fin (Fin.castLE _ i).val` and `Fin i.val`, which agree by
  -- definition; a rewrite cannot change this type argument without changing the map's type.
  rfl

/-- **Truncation commutes with coordinate changes** of symmetric jets, where the coordinate maps
are `C^r'`. -/
theorem SymmetricJet.truncate_symmetricJetCoordChange {r' r : ℕ} (hr : r' ≤ r) {h : E' → E}
    {g : E' → F →L[𝕜] G} {x : E'} (hh : ContDiffAt 𝕜 r' h x) (hg : ContDiffAt 𝕜 r' g x)
    (A : SymmetricJet 𝕜 E F r) :
    SymmetricJet.truncate 𝕜 E' G hr (symmetricJetCoordChange r h g x A) =
      symmetricJetCoordChange r' h g x (SymmetricJet.truncate 𝕜 E F hr A) := by
  rw [symmetricJetCoordChange_apply, SymmetricJet.truncate_jetSymmetrize,
    symmetricJetCoordChange_apply, SymmetricJet.coeFn_truncate,
    funext (jetTruncate_apply hr (linearJetCoordChange r h g x ⇑A)),
    funext (jetTruncate_apply hr ⇑A)]
  exact congrArg _ (linearJetCoordChange_truncate hr hh hg ⇑A)

end TauCeti

/-! ### Smoothness of coordinate changes of symmetric jets -/

open TauCeti

/-- **Smoothness of coordinate changes of symmetric jets.** If the coordinate maps `h` and `g` are
`C^n` at `x₀`, then the coordinate change of symmetric `r`-jets is `C^m` at `x₀` as a continuous
linear map, provided `m + r ≤ n`. -/
theorem ContDiffAt.symmetricJetCoordChange {r : ℕ} {h : E' → E} {g : E' → F →L[𝕜] G} {x₀ : E'}
    {n m : ℕ∞ω} (hh : ContDiffAt 𝕜 n h x₀) (hg : ContDiffAt 𝕜 n g x₀) (hmn : m + r ≤ n) :
    ContDiffAt 𝕜 m (TauCeti.symmetricJetCoordChange r h g) x₀ := by
  -- By definition, `symmetricJetCoordChange r h g x` is this composite (with `∘L` associating to
  -- the right), so the goal changes by unfolding it.
  change ContDiffAt 𝕜 m (fun x ↦ jetSymmetrize 𝕜 E' G r ∘L
    (TauCeti.linearJetCoordChange r h g x ∘L SymmetricJet.subtypeL 𝕜 E F r)) x₀
  -- Composing with the symmetrization and the inclusion is continuous linear in the operator.
  exact (contDiff_const.clm_comp (contDiff_id.clm_comp contDiff_const)).contDiffAt.comp x₀
    (hh.linearJetCoordChange hg hmn)

/-- **Smoothness of coordinate changes of symmetric jets on open sets.** If the coordinate maps
`h` and `g` are `C^n` on an open set `u`, such as a chart overlap, then the coordinate change of
symmetric `r`-jets is `C^m` on `u` as a continuous linear map, provided `m + r ≤ n`. -/
theorem ContDiffOn.symmetricJetCoordChange {r : ℕ} {h : E' → E} {g : E' → F →L[𝕜] G}
    {u : Set E'} {n m : ℕ∞ω} (hu : IsOpen u) (hh : ContDiffOn 𝕜 n h u) (hg : ContDiffOn 𝕜 n g u)
    (hmn : m + r ≤ n) :
    ContDiffOn 𝕜 m (TauCeti.symmetricJetCoordChange r h g) u := fun _ hx ↦
  ((hh.contDiffAt (hu.mem_nhds hx)).symmetricJetCoordChange (hg.contDiffAt (hu.mem_nhds hx))
    hmn).contDiffWithinAt
