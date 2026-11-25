/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.Analysis.Calculus.Jet.HigherOrder
public import TauCeti.Analysis.Calculus.Jet.LinearCoordChange
public import TauCeti.Topology.Algebra.Module.FiniteDimension
public import TauCeti.Topology.Algebra.Module.Multilinear.Symmetrize

/-!
# Symmetric jets and their coordinate changes

The `r`-jet at a point of a `C^r` map `s : E → F` over `ℝ` or `ℂ` is the tuple
`(D⁰ s(y), D¹ s(y), …, Dʳ s(y))` of its iterated derivatives, and each `Dⁱ s(y)` is a symmetric
multilinear map. The tuples all of whose components are symmetric form the closed subspace
`TauCeti.symmetricJets 𝕜 E F r`, and every symmetric tuple is the jet of its Taylor polynomial.
This subspace is the fibre of the bundle of `r`-jets of a vector bundle.

The coordinate change of jets `TauCeti.linearJetCoordChange` is defined on all tuples, but its
identity law only holds on symmetric ones. Over a field of characteristic zero, taking the jet
at `0` of the Taylor polynomial at `0` is a continuous linear projection onto the symmetric
jets, the symmetrization `TauCeti.symmetrizeJets`, which averages each component over the
permutations of its arguments (`TauCeti.toJets_symmetrizeJets_apply`). Composing with it gives
the coordinate change of symmetric jets `TauCeti.symmetricJetCoordChange`, an operator on the
symmetric jets which is defined for all coordinate maps. When the coordinate maps are smooth
enough it is the restriction of `linearJetCoordChange`, and it then satisfies the identity and
cocycle laws on the nose, so it can serve as the transition function of a vector bundle. It
commutes with the truncation of symmetric jets to lower order.

## Main declarations

* `TauCeti.isClosed_symmetricJets`: the symmetric `r`-jets `TauCeti.symmetricJets` form a
  closed subspace of all tuples, and `TauCeti.SymmetricJet` is the same space as a normed space.
* `TauCeti.iteratedFDeriv_mem_symmetricJets`: jets of `C^r` maps are symmetric.
* `TauCeti.symmetrizeJets`: the continuous linear projection onto the symmetric jets
  (`TauCeti.symmetrizeJets_of_mem`), which fixes jets of maps
  (`TauCeti.toJets_symmetrizeJets_iteratedFDeriv`) and symmetrizes each component
  (`TauCeti.toJets_symmetrizeJets_apply`).
* `TauCeti.symmetricJetCoordChange`: the coordinate change of symmetric jets, with its
  identity and cocycle laws `TauCeti.symmetricJetCoordChange_id` and
  `TauCeti.symmetricJetCoordChange_comp`, its action on jets of maps
  `TauCeti.toJets_symmetricJetCoordChange_iteratedFDeriv`, its dependence on germs only
  `TauCeti.symmetricJetCoordChange_congr`, and its smoothness
  `ContDiffAt.symmetricJetCoordChange` and `ContDiffOn.symmetricJetCoordChange`.
* `TauCeti.SymmetricJet.truncate`: truncation of symmetric jets to lower order, which commutes
  with coordinate changes (`TauCeti.SymmetricJet.truncate_symmetricJetCoordChange`).

## Implementation notes

`TauCeti.SymmetricJet` is a type synonym for the subtype of `symmetricJets` carrying only its
normed structure. On the subtype itself, instance search finds the topology induced from the
operator topology of multilinear maps and does not identify it with the topology of the subspace
norm, so it finds no norm on continuous linear maps between such subtypes; these are the
coordinate changes of the jet bundle.

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

variable {r : ℕ}

/-- The symmetric jets form a closed subspace. -/
theorem isClosed_symmetricJets :
    IsClosed (symmetricJets 𝕜 E F r : Set ((i : Fin (r + 1)) → E [×i.val]→L[𝕜] F)) := by
  have : (symmetricJets 𝕜 E F r : Set ((i : Fin (r + 1)) → E [×i.val]→L[𝕜] F)) =
      ⋂ (i : Fin (r + 1)) (v : Fin i.val → E) (σ : Perm (Fin i.val)),
        {A | A i (v ∘ σ) = A i v} := by
    ext A
    simp [mem_symmetricJets]
  rw [this]
  refine isClosed_iInter fun i ↦ isClosed_iInter fun v ↦ isClosed_iInter fun σ ↦ ?_
  have hc : Continuous fun A : (i : Fin (r + 1)) → E [×i.val]→L[𝕜] F ↦ A i :=
    continuous_apply i
  exact isClosed_eq ((continuous_eval_const _).comp hc) ((continuous_eval_const _).comp hc)

variable (𝕜 E F r) in
/-- The type of **symmetric `r`-jets**, the subspace `TauCeti.symmetricJets 𝕜 E F r` as a normed
space. It is the model fibre of the bundle of `r`-jets of a vector bundle. -/
def SymmetricJet : Type _ :=
  symmetricJets 𝕜 E F r

instance : NormedAddCommGroup (SymmetricJet 𝕜 E F r) :=
  inferInstanceAs (NormedAddCommGroup (symmetricJets 𝕜 E F r))

instance : NormedSpace 𝕜 (SymmetricJet 𝕜 E F r) :=
  inferInstanceAs (NormedSpace 𝕜 (symmetricJets 𝕜 E F r))

/-- The symmetric jets are complete when the target is. -/
instance [CompleteSpace F] : CompleteSpace (SymmetricJet 𝕜 E F r) :=
  have : CompleteSpace (symmetricJets 𝕜 E F r) := isClosed_symmetricJets.completeSpace_coe
  inferInstanceAs (CompleteSpace (symmetricJets 𝕜 E F r))

/-- The symmetric jets between finite-dimensional spaces form a finite-dimensional space. -/
instance [FiniteDimensional 𝕜 E] [FiniteDimensional 𝕜 F] :
    FiniteDimensional 𝕜 (SymmetricJet 𝕜 E F r) :=
  inferInstanceAs (FiniteDimensional 𝕜 (symmetricJets 𝕜 E F r))

namespace SymmetricJet

variable (𝕜 E F r) in
/-- The underlying tuple of a symmetric jet, as a continuous linear map. -/
def toJets : SymmetricJet 𝕜 E F r →L[𝕜] ((i : Fin (r + 1)) → E [×i.val]→L[𝕜] F) :=
  (symmetricJets 𝕜 E F r).subtypeL

/-- The symmetric jet with a given symmetric tuple. -/
def mk (A : (i : Fin (r + 1)) → E [×i.val]→L[𝕜] F) (hA : A ∈ symmetricJets 𝕜 E F r) :
    SymmetricJet 𝕜 E F r :=
  ⟨A, hA⟩

/-- The tuple of `SymmetricJet.mk A hA` is `A`. -/
@[simp]
theorem toJets_mk (A : (i : Fin (r + 1)) → E [×i.val]→L[𝕜] F)
    (hA : A ∈ symmetricJets 𝕜 E F r) : toJets 𝕜 E F r (mk A hA) = A :=
  (rfl)

/-- The tuple of a symmetric jet is symmetric. -/
theorem toJets_mem (A : SymmetricJet 𝕜 E F r) : toJets 𝕜 E F r A ∈ symmetricJets 𝕜 E F r :=
  A.property

/-- A symmetric jet is determined by its tuple. -/
theorem toJets_injective : Function.Injective (toJets 𝕜 E F r) :=
  Subtype.val_injective

/-- Symmetric jets with the same tuples are equal. -/
@[ext]
theorem ext {A B : SymmetricJet 𝕜 E F r} (h : toJets 𝕜 E F r A = toJets 𝕜 E F r B) : A = B :=
  toJets_injective h

/-- Rebuilding a symmetric jet from its tuple gives it back. -/
@[simp]
theorem mk_toJets (A : SymmetricJet 𝕜 E F r) : mk (toJets 𝕜 E F r A) (toJets_mem A) = A :=
  (rfl)

end SymmetricJet

/-- **Jets of maps are symmetric.** If `f` is `C^n` at `x` with `minSmoothness 𝕜 r ≤ n` (`C^r`
over `ℝ` or `ℂ`, analytic otherwise), its `r`-jet at `x` is a symmetric jet. -/
theorem iteratedFDeriv_mem_symmetricJets {f : E → F} {x : E} {n : ℕ∞ω}
    (hf : ContDiffAt 𝕜 n f x) (hn : minSmoothness 𝕜 r ≤ n) :
    (fun i : Fin (r + 1) ↦ iteratedFDeriv 𝕜 i.val f x) ∈ symmetricJets 𝕜 E F r :=
  mem_symmetricJets.2 fun i v σ ↦ hf.iteratedFDeriv_comp_perm_of_le
    ((minSmoothness_monotone (by exact_mod_cast i.is_le)).trans hn) v σ

/-- **Coordinate changes produce symmetric jets.** If the coordinate maps are `C^n` at `x` with
`minSmoothness 𝕜 r ≤ n`, every transformed jet is symmetric. -/
theorem linearJetCoordChange_mem_symmetricJets {h : E' → E} {g : E' → F →L[𝕜] G} {x : E'}
    {n : ℕ∞ω} (hh : ContDiffAt 𝕜 n h x) (hg : ContDiffAt 𝕜 n g x) (hn : minSmoothness 𝕜 r ≤ n)
    (A : (i : Fin (r + 1)) → E [×i.val]→L[𝕜] F) :
    linearJetCoordChange r h g x A ∈ symmetricJets 𝕜 E' G r :=
  mem_symmetricJets.2 fun i v σ ↦ linearJetCoordChange_apply_comp_perm i hh hg
    ((minSmoothness_monotone (by exact_mod_cast i.is_le)).trans hn) A v σ

/-! ### Symmetrization -/

open SymmetricJet

variable (𝕜 E F r) in
/-- The **symmetrization of jets**. It sends a tuple to the `r`-jet at `0` of its Taylor
polynomial at `0` (`TauCeti.toJets_symmetrizeJets`), which averages each component over the
permutations of its arguments. Over a field of characteristic zero it is a continuous linear
projection of all tuples onto the symmetric jets (`TauCeti.symmetrizeJets_of_mem`). -/
def symmetrizeJets :
    ((i : Fin (r + 1)) → E [×i.val]→L[𝕜] F) →L[𝕜] SymmetricJet 𝕜 E F r :=
  (linearJetCoordChange r id (fun _ ↦ ContinuousLinearMap.id 𝕜 F) 0).codRestrict _
    (linearJetCoordChange_mem_symmetricJets (n := ω) contDiffAt_id contDiffAt_const le_top)

/-- The tuple of the symmetrization of a tuple is its coordinate change of jets under the identity
coordinate changes at `0`. -/
theorem toJets_symmetrizeJets_eq_linearJetCoordChange
    (A : (i : Fin (r + 1)) → E [×i.val]→L[𝕜] F) :
    toJets 𝕜 E F r (symmetrizeJets 𝕜 E F r A) =
      linearJetCoordChange r id (fun _ ↦ ContinuousLinearMap.id 𝕜 F) 0 A :=
  (rfl)

/-- The symmetrization of a tuple is the `r`-jet at `0` of its Taylor polynomial at `0`. -/
theorem toJets_symmetrizeJets (A : (i : Fin (r + 1)) → E [×i.val]→L[𝕜] F) :
    toJets 𝕜 E F r (symmetrizeJets 𝕜 E F r A) =
      fun i : Fin (r + 1) ↦ iteratedFDeriv 𝕜 i.val (finiteJetPolynomial r A 0) 0 := by
  rw [toJets_symmetrizeJets_eq_linearJetCoordChange]
  funext i
  exact linearJetCoordChange_apply i contDiffAt_id contDiffAt_const A |>.trans (by simp)

/-- **The symmetrization fixes symmetric jets.** -/
theorem symmetrizeJets_of_mem [CharZero 𝕜] {A : (i : Fin (r + 1)) → E [×i.val]→L[𝕜] F}
    (hA : A ∈ symmetricJets 𝕜 E F r) : symmetrizeJets 𝕜 E F r A = mk A hA :=
  toJets_injective (by
    rw [toJets_symmetrizeJets_eq_linearJetCoordChange, toJets_mk]
    exact linearJetCoordChange_id 0 (mem_symmetricJets.1 hA))

/-- The symmetrization is a left inverse of the inclusion of the symmetric jets. -/
@[simp]
theorem symmetrizeJets_toJets [CharZero 𝕜] (A : SymmetricJet 𝕜 E F r) :
    symmetrizeJets 𝕜 E F r (toJets 𝕜 E F r A) = A :=
  symmetrizeJets_of_mem (toJets_mem A)

/-- The symmetrization composed with the inclusion of the symmetric jets is the identity. -/
@[simp]
theorem symmetrizeJets_comp_toJets [CharZero 𝕜] :
    symmetrizeJets 𝕜 E F r ∘L toJets 𝕜 E F r = ContinuousLinearMap.id 𝕜 _ := by
  ext1 A
  simp

/-- **The symmetrization averages each component.** Over a field of characteristic zero, the
component of order `i` of the symmetrization of a tuple `A` is the average
`ContinuousMultilinearMap.symmetrize` of `A i` over the permutations of its arguments. -/
theorem toJets_symmetrizeJets_apply [CharZero 𝕜] (A : (i : Fin (r + 1)) → E [×i.val]→L[𝕜] F)
    (i : Fin (r + 1)) :
    toJets 𝕜 E F r (symmetrizeJets 𝕜 E F r A) i =
      ContinuousMultilinearMap.symmetrize 𝕜 (Fin i.val) E F (A i) := by
  set B : (i : Fin (r + 1)) → E [×i.val]→L[𝕜] F :=
    fun i ↦ ContinuousMultilinearMap.symmetrize 𝕜 (Fin i.val) E F (A i)
  have hB : B ∈ symmetricJets 𝕜 E F r := mem_symmetricJets.2 fun i v σ ↦
    ContinuousMultilinearMap.symmetrize_apply_comp_perm (A i) v σ
  -- The Taylor polynomials of `A` and `B` only see the diagonal values, on which they agree.
  have hpoly : finiteJetPolynomial r B 0 = finiteJetPolynomial r A 0 := by
    funext y
    simp only [finiteJetPolynomial_apply, B,
      ContinuousMultilinearMap.symmetrize_apply_const]
  have hAB : toJets 𝕜 E F r (symmetrizeJets 𝕜 E F r A) =
      toJets 𝕜 E F r (symmetrizeJets 𝕜 E F r B) := by
    rw [toJets_symmetrizeJets, toJets_symmetrizeJets, hpoly]
  rw [hAB, symmetrizeJets_of_mem hB, toJets_mk]

/-- **Symmetrizing the jet of a map does nothing.** If `f` is `C^n` at `x` with
`minSmoothness 𝕜 r ≤ n` (`C^r` over `ℝ` or `ℂ`, analytic otherwise), the symmetrization of its
`r`-jet at `x` has the same tuple. -/
theorem toJets_symmetrizeJets_iteratedFDeriv [CharZero 𝕜] {f : E → F} {x : E} {n : ℕ∞ω}
    (hf : ContDiffAt 𝕜 n f x) (hn : minSmoothness 𝕜 r ≤ n) :
    toJets 𝕜 E F r (symmetrizeJets 𝕜 E F r fun i : Fin (r + 1) ↦ iteratedFDeriv 𝕜 i.val f x) =
      fun i : Fin (r + 1) ↦ iteratedFDeriv 𝕜 i.val f x := by
  rw [symmetrizeJets_of_mem (iteratedFDeriv_mem_symmetricJets hf hn), toJets_mk]

/-! ### Coordinate changes of symmetric jets -/

/-- The **coordinate change of symmetric `r`-jets** under a change of base coordinates
`h : E' → E` and a base-dependent linear change of fibre coordinates `g : E' → F →L[𝕜] G`, at
`x : E'`. It is the coordinate change of jets `TauCeti.linearJetCoordChange` followed by the
symmetrization, so it is defined for all `h` and `g`; when they are smooth enough near `x` the
symmetrization does nothing (`TauCeti.toJets_symmetricJetCoordChange`). -/
def symmetricJetCoordChange (r : ℕ) (h : E' → E) (g : E' → F →L[𝕜] G) (x : E') :
    SymmetricJet 𝕜 E F r →L[𝕜] SymmetricJet 𝕜 E' G r :=
  symmetrizeJets 𝕜 E' G r ∘L linearJetCoordChange r h g x ∘L toJets 𝕜 E F r

/-- Unfolding the coordinate change of symmetric jets. -/
theorem symmetricJetCoordChange_apply (r : ℕ) (h : E' → E) (g : E' → F →L[𝕜] G) (x : E')
    (A : SymmetricJet 𝕜 E F r) :
    symmetricJetCoordChange r h g x A =
      symmetrizeJets 𝕜 E' G r (linearJetCoordChange r h g x (toJets 𝕜 E F r A)) :=
  (rfl)

/-- If the coordinate maps are `C^n` at `x` with `minSmoothness 𝕜 r ≤ n`, the coordinate change of
symmetric jets is the coordinate change of jets. -/
theorem toJets_symmetricJetCoordChange [CharZero 𝕜] {h : E' → E} {g : E' → F →L[𝕜] G} {x : E'}
    {n : ℕ∞ω} (hh : ContDiffAt 𝕜 n h x) (hg : ContDiffAt 𝕜 n g x) (hn : minSmoothness 𝕜 r ≤ n)
    (A : SymmetricJet 𝕜 E F r) :
    toJets 𝕜 E' G r (symmetricJetCoordChange r h g x A) =
      linearJetCoordChange r h g x (toJets 𝕜 E F r A) := by
  rw [symmetricJetCoordChange_apply,
    symmetrizeJets_of_mem (linearJetCoordChange_mem_symmetricJets hh hg hn _), toJets_mk]

/-- Coordinate changes of symmetric jets depend only on the germs of the coordinate maps. -/
theorem symmetricJetCoordChange_congr {h h' : E' → E} {g g' : E' → F →L[𝕜] G} {x : E'}
    (hh : h =ᶠ[𝓝 x] h') (hg : g =ᶠ[𝓝 x] g') :
    symmetricJetCoordChange r h g x = symmetricJetCoordChange r h' g' x := by
  rw [symmetricJetCoordChange, symmetricJetCoordChange, linearJetCoordChange_congr hh hg]

/-- **The identity law.** The identity coordinate change fixes every symmetric jet. -/
@[simp]
theorem symmetricJetCoordChange_id [CharZero 𝕜] (x : E) :
    symmetricJetCoordChange r id (fun _ ↦ ContinuousLinearMap.id 𝕜 F) x =
      ContinuousLinearMap.id 𝕜 _ := by
  ext1 A
  exact toJets_injective ((toJets_symmetricJetCoordChange (n := ω) contDiffAt_id
    contDiffAt_const le_top A).trans
      (linearJetCoordChange_id x (mem_symmetricJets.1 (toJets_mem A))))

/-- **The cocycle law.** If `h₁` and `g₁` are `C^n` at `h₂ x`, with `minSmoothness 𝕜 r ≤ n`
(`C^r` over `ℝ` or `ℂ`, analytic otherwise), and `h₂` and `g₂` are `C^r` at `x`, then transforming a
symmetric jet first by `(h₁, g₁)` at `h₂ x` and then by `(h₂, g₂)` at `x` is transforming it by
the composite coordinate change `(h₁ ∘ h₂, z ↦ g₂ z ∘ g₁ (h₂ z))` at `x`. -/
theorem symmetricJetCoordChange_comp [CharZero 𝕜] {n : ℕ∞ω} {h₁ : E' → E}
    {g₁ : E' → F →L[𝕜] G} {h₂ : E'' → E'} {g₂ : E'' → G →L[𝕜] H} {x : E''}
    (hh₁ : ContDiffAt 𝕜 n h₁ (h₂ x)) (hg₁ : ContDiffAt 𝕜 n g₁ (h₂ x))
    (hh₂ : ContDiffAt 𝕜 r h₂ x) (hg₂ : ContDiffAt 𝕜 r g₂ x) (hn : minSmoothness 𝕜 r ≤ n)
    (A : SymmetricJet 𝕜 E F r) :
    symmetricJetCoordChange r h₂ g₂ x (symmetricJetCoordChange r h₁ g₁ (h₂ x) A) =
      symmetricJetCoordChange r (h₁ ∘ h₂) (fun z ↦ (g₂ z).comp (g₁ (h₂ z))) x A := by
  rw [symmetricJetCoordChange_apply r h₂, toJets_symmetricJetCoordChange hh₁ hg₁ hn,
    linearJetCoordChange_comp hh₁ hg₁ hn hh₂ hg₂,
    symmetricJetCoordChange_apply]

/-- **Coordinate changes of jets of maps.** If `h` and `g` are `C^n` at `x` and `s` is `C^n` at
`h x` with `minSmoothness 𝕜 r ≤ n` (`C^r` over `ℝ` or `ℂ`, analytic otherwise), the coordinate
change of symmetric jets takes the `r`-jet of `s` at `h x` to the `r`-jet at `x` of the
transformed map `z ↦ g z (s (h z))`. -/
theorem toJets_symmetricJetCoordChange_iteratedFDeriv [CharZero 𝕜] {n : ℕ∞ω} {h : E' → E}
    {g : E' → F →L[𝕜] G} {x : E'} {s : E → F} (hs : ContDiffAt 𝕜 n s (h x))
    (hn : minSmoothness 𝕜 r ≤ n) (hh : ContDiffAt 𝕜 n h x) (hg : ContDiffAt 𝕜 n g x) :
    toJets 𝕜 E' G r (symmetricJetCoordChange r h g x
        (mk (fun i : Fin (r + 1) ↦ iteratedFDeriv 𝕜 i.val s (h x))
          (iteratedFDeriv_mem_symmetricJets hs hn))) =
      fun i : Fin (r + 1) ↦ iteratedFDeriv 𝕜 i.val (fun z ↦ g z (s (h z))) x := by
  have hr : (r : ℕ∞ω) ≤ n := le_minSmoothness.trans hn
  rw [toJets_symmetricJetCoordChange hh hg hn, toJets_mk]
  exact linearJetCoordChange_iteratedFDeriv hs hn (hh.of_le hr) (hg.of_le hr)

/-! ### Truncation of symmetric jets -/

namespace SymmetricJet

variable {r' : ℕ}

variable (𝕜 E F) in
/-- The **truncation** of symmetric `r`-jets to order `r' ≤ r`, forgetting the components of
order greater than `r'`: the truncation `TauCeti.jetTruncate` of their tuples
(`TauCeti.SymmetricJet.toJets_truncate`). -/
def truncate (hr : r' ≤ r) : SymmetricJet 𝕜 E F r →L[𝕜] SymmetricJet 𝕜 E F r' :=
  (ContinuousLinearMap.pi fun i : Fin (r' + 1) ↦
    (ContinuousLinearMap.proj (R := 𝕜) (φ := fun i : Fin (r + 1) ↦ E [×i.val]→L[𝕜] F)
      (i.castLE (Nat.add_le_add_right hr 1))).comp (toJets 𝕜 E F r)).codRestrict
    (symmetricJets 𝕜 E F r') fun A ↦ mem_symmetricJets.2 fun i v σ ↦
      mem_symmetricJets.1 (toJets_mem A) (i.castLE (Nat.add_le_add_right hr 1)) v σ

/-- The tuple of a truncated jet is the truncation of its tuple. -/
@[simp]
theorem toJets_truncate (hr : r' ≤ r) (A : SymmetricJet 𝕜 E F r) :
    toJets 𝕜 E F r' (truncate 𝕜 E F hr A) = jetTruncate hr (toJets 𝕜 E F r A) :=
  funext fun i ↦ (jetTruncate_apply hr _ i).symm

/-- Truncating to the same order is the identity. -/
@[simp]
theorem truncate_rfl : truncate 𝕜 E F (le_refl r) = ContinuousLinearMap.id 𝕜 _ := by
  ext1 A
  exact toJets_injective ((toJets_truncate _ A).trans (jetTruncate_refl r _))

/-- Truncations compose. -/
@[simp]
theorem truncate_comp_truncate {r'' : ℕ} (hr' : r'' ≤ r') (hr : r' ≤ r) :
    truncate 𝕜 E F hr' ∘L truncate 𝕜 E F hr = truncate 𝕜 E F (hr'.trans hr) := by
  ext1 A
  refine toJets_injective ?_
  simp only [ContinuousLinearMap.comp_apply, toJets_truncate, jetTruncate_trans]

/-- Truncation commutes with the symmetrization. -/
theorem truncate_symmetrizeJets (hr : r' ≤ r) (A : (i : Fin (r + 1)) → E [×i.val]→L[𝕜] F) :
    truncate 𝕜 E F hr (symmetrizeJets 𝕜 E F r A) =
      symmetrizeJets 𝕜 E F r' (jetTruncate hr A) := by
  refine toJets_injective ?_
  rw [toJets_truncate, toJets_symmetrizeJets_eq_linearJetCoordChange,
    toJets_symmetrizeJets_eq_linearJetCoordChange, funext (jetTruncate_apply hr _),
    funext (jetTruncate_apply hr A)]
  exact linearJetCoordChange_truncate hr contDiffAt_id contDiffAt_const A

/-- **Truncation commutes with coordinate changes** of symmetric jets, where the coordinate maps
are `C^r'`. -/
theorem truncate_symmetricJetCoordChange (hr : r' ≤ r) {h : E' → E} {g : E' → F →L[𝕜] G}
    {x : E'} (hh : ContDiffAt 𝕜 r' h x) (hg : ContDiffAt 𝕜 r' g x) (A : SymmetricJet 𝕜 E F r) :
    truncate 𝕜 E' G hr (symmetricJetCoordChange r h g x A) =
      symmetricJetCoordChange r' h g x (truncate 𝕜 E F hr A) := by
  rw [symmetricJetCoordChange_apply, truncate_symmetrizeJets, symmetricJetCoordChange_apply,
    toJets_truncate, funext (jetTruncate_apply hr (linearJetCoordChange r h g x _)),
    funext (jetTruncate_apply hr (toJets 𝕜 E F r A))]
  exact congrArg _ (linearJetCoordChange_truncate hr hh hg _)

end SymmetricJet

end TauCeti

open TauCeti

/-- **Smoothness of coordinate changes of symmetric jets.** If the coordinate maps `h` and `g` are
`C^n` at `x₀`, then the coordinate change of symmetric `r`-jets is `C^m` at `x₀` as a continuous
linear map, provided `m + r ≤ n`. -/
theorem ContDiffAt.symmetricJetCoordChange {r : ℕ} {h : E' → E} {g : E' → F →L[𝕜] G} {x₀ : E'}
    {n m : ℕ∞ω} (hh : ContDiffAt 𝕜 n h x₀) (hg : ContDiffAt 𝕜 n g x₀) (hmn : m + r ≤ n) :
    ContDiffAt 𝕜 m (symmetricJetCoordChange r h g) x₀ := by
  -- By definition, `symmetricJetCoordChange r h g x` is this composite (with `∘L` associating to
  -- the right), so the goal changes by unfolding it.
  change ContDiffAt 𝕜 m (fun x ↦ symmetrizeJets 𝕜 E' G r ∘L
    (TauCeti.linearJetCoordChange r h g x ∘L SymmetricJet.toJets 𝕜 E F r)) x₀
  -- Composing with the symmetrization and the inclusion is continuous linear in the operator.
  exact (contDiff_const.clm_comp (contDiff_id.clm_comp contDiff_const)).contDiffAt.comp x₀
    (hh.linearJetCoordChange hg hmn)

/-- **Smoothness of coordinate changes of symmetric jets on open sets.** If the coordinate maps
`h` and `g` are `C^n` on an open set `u`, such as a chart overlap, then the coordinate change of
symmetric `r`-jets is `C^m` on `u` as a continuous linear map, provided `m + r ≤ n`. -/
theorem ContDiffOn.symmetricJetCoordChange {r : ℕ} {h : E' → E}
    {g : E' → F →L[𝕜] G} {u : Set E'} {n m : ℕ∞ω} (hu : IsOpen u) (hh : ContDiffOn 𝕜 n h u)
    (hg : ContDiffOn 𝕜 n g u) (hmn : m + r ≤ n) :
    ContDiffOn 𝕜 m (symmetricJetCoordChange r h g) u :=
  contDiffOn_const.clm_comp ((hh.linearJetCoordChange hu hg hmn).clm_comp contDiffOn_const)
