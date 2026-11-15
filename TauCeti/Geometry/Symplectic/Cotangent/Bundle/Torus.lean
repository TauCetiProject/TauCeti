/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import Mathlib.Topology.Maps.Proper.Basic
public import TauCeti.Geometry.Manifold.DeRham.Torus
public import TauCeti.Geometry.Manifold.VectorBundle.Tangent.Basic
public import TauCeti.Geometry.Symplectic.Cotangent.Bundle.Graph

import TauCeti.Geometry.Manifold.LocalDiffeomorph.Basic
import TauCeti.Geometry.Manifold.LocalDiffeomorph.Prod.Basic
import TauCeti.Geometry.Manifold.VectorBundle.FrameTrivialization

/-!
# Action–angle coordinates and Lagrangian sections on the cotangent bundle of a torus

For a finite family of positive periods `p i`, let `Tⁿ = ∀ i, AddCircle (p i)` be the torus with
product model `IT = ModelWithCorners.pi fun _ ↦ 𝓘(ℝ)` and coordinate time forms `dt_i`
(`TauCeti.torusTimeForm p i`). Because the forms `dt_i` form a global smooth frame of the cotangent
bundle `T*Tⁿ` (`TauCeti.isLocalFrameOn_torusTimeForm`), expanding covectors in this frame gives a
smooth global trivialization

`(Tⁿ × (ι → ℝ)) ≃ₘ T*Tⁿ`, `(θ, I) ↦ (θ, ∑ i, I i • dt_i)`

(`TauCeti.CotangentBundle.torusTrivializationDiffeomorph`), whose inverse sends a covector `ξ` to
its base angle `ξ.proj` and its action vector `i ↦ ξ.2 (Pi.single i 1)`. The action projection
`ξ ↦ (ξ.2 (e_i))_i` is smooth and proper (`TauCeti.CotangentBundle.contMDiff_torusAction`,
`TauCeti.CotangentBundle.isProperMap_torusAction`), and its fibre over `I` is the torus graph of
`∑ i, I i • dt_i` (`TauCeti.CotangentBundle.range_torusTrivializationDiffeomorph_mk`).

Precomposing with the quotient covering `(ι → ℝ) → Tⁿ` yields the surjective local diffeomorphism
`TauCeti.CotangentBundle.torusCover p : (ι → ℝ) × (ι → ℝ) → T*Tⁿ`, whose fibres are the
period-lattice translates in the angle factor (`TauCeti.CotangentBundle.torusCover_eq_iff`). It
pulls the Liouville form back to `∑ i, I i dθ_i`
(`TauCeti.CotangentBundle.mpullback_torusCover_liouvilleForm_apply`) and the canonical symplectic
form `ω = -dλ` back to the standard linear form `∑ i, (a i * b' i - a' i * b i)`
(`TauCeti.CotangentBundle.eval₂_symplecticForm_mfderiv_torusCover`); the same formulas hold for
`torusTrivializationDiffeomorph`
(`TauCeti.CotangentBundle.mpullback_torusTrivializationDiffeomorph_liouvilleForm_apply`,
`TauCeti.CotangentBundle.eval₂_mpullback_torusTrivializationDiffeomorph_symplecticForm`).

This file also records the Lagrangian properties of the constant-coefficient angle sections
`α_c = ∑ j, c j • dt_j`:

* The graph of `α_c` is a Lagrangian map for every `c`, since `α_c` is closed
  (`TauCeti.CotangentBundle.isLagrangianMap_section_sum_smul_torusTimeForm`).
* It is an exact Lagrangian map, for the primitive `λ` of `ω` and some primitive on the torus,
  exactly when `c = 0`, that is when it is the zero section
  (`TauCeti.CotangentBundle.exists_isExactLagrangianMap_section_sum_smul_torusTimeForm_iff`). This
  is because `α_c` integrates to `c i * p i` around the `i`-th coordinate circle.
* For `c ≠ 0` the graph of `α_c` meets the zero section nowhere
  (`TauCeti.CotangentBundle.section_sum_smul_torusTimeForm_eq_zeroSection_iff`).

## Main definitions

* `TauCeti.CotangentBundle.torusCover`: the covering map
  `(ι → ℝ) × (ι → ℝ) → T*(∀ i, AddCircle (p i))`.
* `TauCeti.CotangentBundle.torusTrivializationDiffeomorph`: the smooth global trivialization
  `((∀ i, AddCircle (p i)) × (ι → ℝ)) ≃ₘ T*(∀ i, AddCircle (p i))` in angle–action coordinates.

## References

* V. I. Arnold, *Mathematical Methods of Classical Mechanics*, 2nd ed., Graduate Texts in
  Mathematics 60, Springer, 1989, Sections 49–50.
* A. Cannas da Silva, *Lectures on Symplectic Geometry*, Lecture Notes in Mathematics 1764,
  Springer, 2001, Sections 3 and 18.4.
* D. McDuff, D. Salamon, *Introduction to Symplectic Topology*, 3rd ed., Oxford, 2017,
  Section 3.2.
-/

public section

noncomputable section

open Bundle Function Set Topology
open scoped Manifold ContDiff

namespace TauCeti

namespace CotangentBundle

variable {ι : Type*} [Fintype ι] (p : ι → ℝ) [∀ i, Fact (0 < p i)]

/-! ### Covering map and global action–angle trivialization of `T*Tⁿ` -/

section Trivialization

/-- The covering map `(ι → ℝ) × (ι → ℝ) → T*(∀ i, AddCircle (p i))` sending `(ϑ, c)` to the value
at `([ϑ i])ᵢ` of the constant-coefficient angle one-form `∑ i, c i • dt_i`. -/
def torusCover (y : (ι → ℝ) × (ι → ℝ)) :
    CotangentBundle (ModelWithCorners.pi fun _ : ι ↦ 𝓘(ℝ)) (∀ i, AddCircle (p i)) :=
  TotalSpace.mk' ((ι → ℝ) →L[ℝ] ℝ) (fun i ↦ (y.1 i : AddCircle (p i)))
    (SmoothForm.degreeOneEquiv (∑ i, y.2 i • torusTimeForm p i)
      (fun i ↦ (y.1 i : AddCircle (p i))))

/-- The base point of `torusCover p (ϑ, c)` is `([ϑ i])ᵢ`. -/
@[simp]
theorem proj_torusCover (y : (ι → ℝ) × (ι → ℝ)) :
    (torusCover p y).proj = fun i ↦ (y.1 i : AddCircle (p i)) :=
  (rfl)

/-- The covector of `torusCover p (ϑ, c)` evaluates `v` to `∑ i, c i * v i`. -/
@[simp]
theorem torusCover_snd_apply (y : (ι → ℝ) × (ι → ℝ))
    (v : TangentSpace (ModelWithCorners.pi fun _ : ι ↦ 𝓘(ℝ)) (torusCover p y).proj) :
    (torusCover p y).2 v = ∑ i, y.2 i * v i := by
  change SmoothForm.degreeOneEquiv (∑ i, y.2 i • torusTimeForm p i) _ v = _
  rw [SmoothForm.degreeOneEquiv_apply_apply, sum_smul_torusTimeForm_apply]

/-- The `i`-th action of `torusCover p (ϑ, c)` is `c i`. -/
@[simp]
theorem torusCover_snd_apply_single [DecidableEq ι] (y : (ι → ℝ) × (ι → ℝ)) (i : ι) :
    (torusCover p y).2 (Pi.single i 1) = y.2 i :=
  (torusCover_snd_apply p y (Pi.single i 1)).trans (by simp [Pi.single_apply])

private theorem covector_apply_eq_sum [DecidableEq ι] {x : ∀ i, AddCircle (p i)}
    (f : TangentSpace (ModelWithCorners.pi fun _ : ι ↦ 𝓘(ℝ)) x →L[ℝ] ℝ)
    (v : TangentSpace (ModelWithCorners.pi fun _ : ι ↦ 𝓘(ℝ)) x) :
    f v = ∑ i, f (Pi.single i 1) * v i := by
  let e : ι → TangentSpace (ModelWithCorners.pi fun _ : ι ↦ 𝓘(ℝ)) x := fun i ↦ Pi.single i 1
  let w : ι → ℝ := v
  have hv0 : w = ∑ i, w i • Pi.single i 1 := by
    ext j
    simp [Pi.single_apply]
  have hv : v = ∑ i, v i • e i := hv0
  conv_lhs => rw [hv]
  rw [map_sum]
  exact Finset.sum_congr rfl fun i _ ↦ by rw [map_smul, smul_eq_mul, mul_comm]

/-- The covering map `torusCover p` onto the cotangent bundle of `∀ i, AddCircle (p i)` is
surjective. -/
theorem torusCover_surjective : Surjective (torusCover p) := fun ⟨x, f⟩ ↦ by
  classical
  obtain ⟨ϑ, hϑ⟩ := AddCircle.pi_coe_surjective p x
  subst hϑ
  refine ⟨(ϑ, fun i ↦ f (Pi.single i 1)), CotangentBundle.ext rfl fun v ↦ ?_⟩
  exact (torusCover_snd_apply p _ v).trans (covector_apply_eq_sum p f v).symm

/-- Two angle–action pairs in `(ι → ℝ) × (ι → ℝ)` have the same image under `torusCover q` if and
only if their action vectors agree and their angle vectors differ by an integer multiple of the
periods `q i`. -/
theorem torusCover_eq_iff {q : ι → ℝ} [∀ i, Fact (0 < q i)] {y y' : (ι → ℝ) × (ι → ℝ)} :
    torusCover q y = torusCover q y' ↔
      y'.2 = y.2 ∧ ∃ m : ι → ℤ, y'.1 = y.1 + fun i ↦ m i • q i := by
  classical
  refine ⟨fun h ↦ ?_, fun ⟨hc, m, hm⟩ ↦ ?_⟩
  · refine ⟨funext fun i ↦ ?_, AddCircle.pi_coe_eq_iff.1 (congrArg TotalSpace.proj h)⟩
    have hi := congrArg (fun z ↦ z.2 (Pi.single i 1)) h
    simpa using hi.symm
  · have hproj : (fun i ↦ (y.1 i : AddCircle (q i))) = fun i ↦ (y'.1 i : AddCircle (q i)) :=
      AddCircle.pi_coe_eq_iff.2 ⟨m, hm⟩
    dsimp only [torusCover]
    rw [← hc, hproj]

/-- **Global action–angle trivialization of `T*Tⁿ`.** The cotangent bundle of the torus
`∀ i, AddCircle (p i)` is smoothly diffeomorphic to `(∀ i, AddCircle (p i)) × (ι → ℝ)`, sending
`(θ, I)` to the covector `∑ i, I i • dt_i` over `θ` and with inverse sending `ξ` to
`(ξ.proj, fun i ↦ ξ.2 (Pi.single i 1))`. -/
def torusTrivializationDiffeomorph [DecidableEq ι] :
    ((∀ i, AddCircle (p i)) × (ι → ℝ)) ≃ₘ⟮
      (ModelWithCorners.pi fun _ : ι ↦ 𝓘(ℝ)).prod 𝓘(ℝ, ι → ℝ),
      (ModelWithCorners.pi fun _ : ι ↦ 𝓘(ℝ)).prod 𝓘(ℝ, (ι → ℝ) →L[ℝ] ℝ)⟯
    CotangentBundle (ModelWithCorners.pi fun _ : ι ↦ 𝓘(ℝ)) (∀ i, AddCircle (p i)) where
  toFun q := TotalSpace.mk' ((ι → ℝ) →L[ℝ] ℝ) q.1
    (SmoothForm.degreeOneEquiv (∑ i, q.2 i • torusTimeForm p i) q.1)
  invFun z := (z.proj, fun i ↦ z.2 (Pi.single i 1))
  left_inv q := Prod.ext rfl <| funext fun i ↦
    (SmoothForm.degreeOneEquiv_apply_apply (∑ j, q.2 j • torusTimeForm p j) q.1
      (Pi.single i 1)).trans
      ((sum_smul_torusTimeForm_apply p q.2 q.1 _).trans (by simp [Pi.single_apply]))
  right_inv := fun ⟨x, f⟩ ↦ CotangentBundle.ext rfl fun v ↦
    (SmoothForm.degreeOneEquiv_apply_apply (∑ i, f (Pi.single i 1) • torusTimeForm p i) x v).trans
      ((sum_smul_torusTimeForm_apply p (fun i ↦ f (Pi.single i 1)) x _).trans
        (covector_apply_eq_sum p f v).symm)
  contMDiff_toFun := by
    let : ContMDiffVectorBundle ∞ (ι → ℝ)
        (TangentSpace (ModelWithCorners.pi fun _ : ι ↦ 𝓘(ℝ)) : (∀ i, AddCircle (p i)) → Type _)
        (ModelWithCorners.pi fun _ : ι ↦ 𝓘(ℝ)) :=
      TangentBundle.contMDiffVectorBundle
    let hs := isLocalFrameOn_torusTimeForm p
    let b : Module.Basis ι ℝ ((ι → ℝ) →L[ℝ] ℝ) :=
      (Pi.basisFun ℝ ι).dualBasis.map LinearMap.toContinuousLinearMap
    let e := hs.trivialization isOpen_univ b
    have he := hs.trivialization_mem_maximalAtlas isOpen_univ b
    intro q₀
    refine (e.contMDiffAt_iff_of_mem_maximalAtlas he (e.mem_source.2 (by simp [e]))).2
      ⟨contMDiffAt_fst, ?_⟩
    have hcoord (q : (∀ i, AddCircle (p i)) × (ι → ℝ)) :
        (e ⟨q.1, SmoothForm.degreeOneEquiv (∑ i, q.2 i • torusTimeForm p i) q.1⟩).2 =
          b.equivFunL.symm q.2 := by
      have hsec : SmoothForm.degreeOneEquiv (∑ i, q.2 i • torusTimeForm p i) q.1 =
          e.symm q.1 (b.equivFunL.symm q.2) := by
        ext v
        rw [SmoothForm.degreeOneEquiv_apply_apply, sum_smul_torusTimeForm_apply,
          hs.trivialization_symm_apply isOpen_univ b (mem_univ q.1), sum_apply]
        refine Finset.sum_congr rfl fun i _ ↦ ?_
        have hrepr : b.repr (b.equivFunL.symm q.2) i = q.2 i :=
          congrFun (b.equivFunL.apply_symm_apply q.2) i
        rw [smul_apply, SmoothForm.degreeOneEquiv_apply_apply, torusTimeForm_apply, hrepr,
          smul_eq_mul]
      rw [hsec, e.apply_mk_symm (by simp [e])]
    exact (b.equivFunL.symm.contDiff.contMDiff.comp contMDiff_snd q₀).congr_of_eventuallyEq
      (Filter.Eventually.of_forall hcoord)
  contMDiff_invFun := by
    let : ContMDiffVectorBundle ∞ (ι → ℝ)
        (TangentSpace (ModelWithCorners.pi fun _ : ι ↦ 𝓘(ℝ)) : (∀ i, AddCircle (p i)) → Type _)
        (ModelWithCorners.pi fun _ : ι ↦ 𝓘(ℝ)) :=
      TangentBundle.contMDiffVectorBundle
    let hs := isLocalFrameOn_torusTimeForm p
    let b : Module.Basis ι ℝ ((ι → ℝ) →L[ℝ] ℝ) :=
      (Pi.basisFun ℝ ι).dualBasis.map LinearMap.toContinuousLinearMap
    let e := hs.trivialization isOpen_univ b
    have he := hs.trivialization_mem_maximalAtlas isOpen_univ b
    refine (contMDiff_proj _).prodMk fun z₀ ↦ ?_
    have hez : ContMDiffAt _ 𝓘(ℝ, (ι → ℝ) →L[ℝ] ℝ) ∞ (fun z ↦ (e z).2) z₀ :=
      ((e.contMDiffAt_iff_of_mem_maximalAtlas he (e.mem_source.2 (by simp [e]))).1
        contMDiffAt_id).2
    have hact (z : CotangentBundle (ModelWithCorners.pi fun _ : ι ↦ 𝓘(ℝ))
        (∀ i, AddCircle (p i))) :
        (fun i ↦ z.2 (Pi.single i 1)) = b.equivFunL (e z).2 := by
      ext i
      let ei : TangentSpace (ModelWithCorners.pi fun _ : ι ↦ 𝓘(ℝ)) z.proj := Pi.single i 1
      have hsymm := e.symm_apply_apply_mk (by simp [e]) z.2
      change e.symm z.proj (e z).2 = z.2 at hsymm
      change z.2 ei = b.equivFunL (e z).2 i
      rw [← hsymm, hs.trivialization_symm_apply isOpen_univ b (mem_univ z.proj), sum_apply]
      simp only [smul_apply, SmoothForm.degreeOneEquiv_apply_apply, torusTimeForm_apply]
      change (∑ j, b.repr (e z).2 j • (Pi.single i (1 : ℝ) : ι → ℝ) j) = b.repr (e z).2 i
      simp [Pi.single_apply]
    exact (b.equivFunL.contDiff.contMDiff.contMDiffAt.comp z₀ hez).congr_of_eventuallyEq
      (Filter.Eventually.of_forall hact)

@[simp]
theorem proj_torusTrivializationDiffeomorph [DecidableEq ι]
    (q : (∀ i, AddCircle (p i)) × (ι → ℝ)) :
    (torusTrivializationDiffeomorph p q).proj = q.1 :=
  (rfl)

@[simp]
theorem torusTrivializationDiffeomorph_snd_apply [DecidableEq ι]
    (q : (∀ i, AddCircle (p i)) × (ι → ℝ))
    (v : TangentSpace (ModelWithCorners.pi fun _ : ι ↦ 𝓘(ℝ))
      (torusTrivializationDiffeomorph p q).proj) :
    (torusTrivializationDiffeomorph p q).2 v = ∑ i, q.2 i * v i :=
  (SmoothForm.degreeOneEquiv_apply_apply (∑ i, q.2 i • torusTimeForm p i) q.1 v).trans
    (sum_smul_torusTimeForm_apply p q.2 q.1 _)

@[simp]
theorem torusTrivializationDiffeomorph_snd_apply_single [DecidableEq ι]
    (q : (∀ i, AddCircle (p i)) × (ι → ℝ)) (i : ι) :
    (torusTrivializationDiffeomorph p q).2 (Pi.single i 1) = q.2 i :=
  (torusTrivializationDiffeomorph_snd_apply p q (Pi.single i 1)).trans (by simp [Pi.single_apply])

@[simp]
theorem torusTrivializationDiffeomorph_symm_apply [DecidableEq ι]
    (z : CotangentBundle (ModelWithCorners.pi fun _ : ι ↦ 𝓘(ℝ)) (∀ i, AddCircle (p i))) :
    (torusTrivializationDiffeomorph p).symm z = (z.proj, fun i ↦ z.2 (Pi.single i 1)) :=
  (rfl)

/-- `torusTrivializationDiffeomorph` sends `(θ, c)` to the value at `θ` of the constant-coefficient
angle one-form `∑ i, c i • dt_i`. -/
theorem torusTrivializationDiffeomorph_eq_section [DecidableEq ι]
    (θ : ∀ i, AddCircle (p i)) (c : ι → ℝ) :
    torusTrivializationDiffeomorph p (θ, c) =
      TotalSpace.mk' ((ι → ℝ) →L[ℝ] ℝ) θ
        (SmoothForm.degreeOneEquiv (∑ i, c i • torusTimeForm p i) θ) :=
  (rfl)

/-- The action coordinate map `z ↦ fun i ↦ z.2 (Pi.single i 1)` on `T*(∀ i, AddCircle (p i))` is
smooth. -/
theorem contMDiff_torusAction [DecidableEq ι] :
    ContMDiff ((ModelWithCorners.pi fun _ : ι ↦ 𝓘(ℝ)).prod 𝓘(ℝ, (ι → ℝ) →L[ℝ] ℝ))
      𝓘(ℝ, ι → ℝ) ∞
      (fun z : CotangentBundle (ModelWithCorners.pi fun _ : ι ↦ 𝓘(ℝ)) (∀ i, AddCircle (p i)) ↦
        fun i ↦ z.2 (Pi.single i 1)) :=
  contMDiff_snd.comp (torusTrivializationDiffeomorph p).symm.contMDiff

/-- **The action projection of `T*Tⁿ` is proper.** Because the torus `∀ i, AddCircle (p i)` is
compact, the map `ξ ↦ fun i ↦ ξ.2 (Pi.single i 1)` is a proper map into `ι → ℝ`. -/
theorem isProperMap_torusAction [DecidableEq ι] :
    IsProperMap
      (fun z : CotangentBundle (ModelWithCorners.pi fun _ : ι ↦ 𝓘(ℝ)) (∀ i, AddCircle (p i)) ↦
        fun i ↦ z.2 (Pi.single i 1)) := by
  have h : (fun z : CotangentBundle (ModelWithCorners.pi fun _ : ι ↦ 𝓘(ℝ))
        (∀ i, AddCircle (p i)) ↦ fun i ↦ z.2 (Pi.single i 1)) =
      Prod.snd ∘ (torusTrivializationDiffeomorph p).symm.toHomeomorph := by
    ext z i
    simp
  rw [h]
  exact isProperMap_snd_of_compactSpace.comp
    (torusTrivializationDiffeomorph p).symm.toHomeomorph.isProperMap

/-- The fibre of the action map `ξ ↦ fun i ↦ ξ.2 (Pi.single i 1)` over `c : ι → ℝ` is the torus
image of `θ ↦ torusTrivializationDiffeomorph p (θ, c)`. -/
theorem range_torusTrivializationDiffeomorph_mk [DecidableEq ι] (c : ι → ℝ) :
    range (fun θ ↦ torusTrivializationDiffeomorph p (θ, c)) =
      {z : CotangentBundle (ModelWithCorners.pi fun _ : ι ↦ 𝓘(ℝ)) (∀ i, AddCircle (p i)) |
        (fun i ↦ z.2 (Pi.single i 1)) = c} := by
  ext z
  refine ⟨fun ⟨θ, hθ⟩ ↦ by rw [← hθ]; simp, fun hz ↦ ⟨z.proj, ?_⟩⟩
  rw [← (torusTrivializationDiffeomorph p).right_inv z]
  exact congrArg (torusTrivializationDiffeomorph p) (Prod.ext rfl hz.symm)

/-! ### Smoothness and symplectic pullback of `torusCover` and `torusTrivializationDiffeomorph` -/

/-- `torusCover p` factors through `torusTrivializationDiffeomorph` and the torus covering map
`ϑ ↦ ([ϑ i])ᵢ`. -/
theorem torusCover_eq_torusTrivializationDiffeomorph [DecidableEq ι] (y : (ι → ℝ) × (ι → ℝ)) :
    torusCover p y =
      torusTrivializationDiffeomorph p (fun i ↦ (y.1 i : AddCircle (p i)), y.2) :=
  (rfl)

/-- The covering map `torusCover p` is smooth. -/
theorem contMDiff_torusCover :
    ContMDiff 𝓘(ℝ, (ι → ℝ) × (ι → ℝ))
      ((ModelWithCorners.pi fun _ : ι ↦ 𝓘(ℝ)).prod 𝓘(ℝ, (ι → ℝ) →L[ℝ] ℝ)) ∞ (torusCover p) := by
  classical
  rw [modelWithCornersSelf_prod, ← chartedSpaceSelf_prod]
  exact (torusTrivializationDiffeomorph p).contMDiff.comp
    ((AddCircle.contMDiff_pi_coe p ∞).prodMap contMDiff_id)

/-- The covering map `torusCover p` is a smooth local diffeomorphism. -/
theorem isLocalDiffeomorph_torusCover :
    IsLocalDiffeomorph 𝓘(ℝ, (ι → ℝ) × (ι → ℝ))
      ((ModelWithCorners.pi fun _ : ι ↦ 𝓘(ℝ)).prod 𝓘(ℝ, (ι → ℝ) →L[ℝ] ℝ)) ∞ (torusCover p) := by
  classical
  intro y
  have hcov : IsLocalDiffeomorph 𝓘(ℝ, (ι → ℝ) × (ι → ℝ))
      ((ModelWithCorners.pi fun _ : ι ↦ 𝓘(ℝ)).prod 𝓘(ℝ, ι → ℝ)) ∞
      (Prod.map (fun t : ι → ℝ ↦ fun i ↦ (t i : AddCircle (p i)))
        (id : (ι → ℝ) → (ι → ℝ))) := by
    rw [modelWithCornersSelf_prod, ← chartedSpaceSelf_prod]
    exact (AddCircle.isLocalDiffeomorph_pi_coe p ∞).prodMap
      (Diffeomorph.refl _ _ ∞).isLocalDiffeomorph
  exact (hcov y).comp (hg := (torusTrivializationDiffeomorph p).isLocalDiffeomorph _)

/-- **Action–angle formula for the Liouville form on the cover.** Pulling `liouvilleForm` back along
`torusCover p` evaluates a tangent vector `v 0` at `(ϑ, c)` to `∑ i, c i * (v 0).1 i`. -/
theorem mpullback_torusCover_liouvilleForm_apply (y : (ι → ℝ) × (ι → ℝ))
    (v : Fin 1 → TangentSpace 𝓘(ℝ, (ι → ℝ) × (ι → ℝ)) y) :
    (SmoothForm.mpullback (I := 𝓘(ℝ, (ι → ℝ) × (ι → ℝ))) (torusCover p) (contMDiff_torusCover p)
        (liouvilleForm (ModelWithCorners.pi fun _ : ι ↦ 𝓘(ℝ)) (∀ i, AddCircle (p i)))).1 y v =
      ∑ i, y.2 i * (v 0 : (ι → ℝ) × (ι → ℝ)).1 i := by
  let g : (ι → ℝ) × (ι → ℝ) → ∀ i, AddCircle (p i) :=
    (fun t : ι → ℝ ↦ fun i ↦ (t i : AddCircle (p i))) ∘ Prod.fst
  rw [SmoothForm.coe_mpullback,
    mpullback_liouvilleForm_apply_of_proj_comp_eq (g := g) (fun _ ↦ rfl)
      ((contMDiff_torusCover p y).mdifferentiableAt (by simp))]
  have hg : mfderiv 𝓘(ℝ, (ι → ℝ) × (ι → ℝ)) (ModelWithCorners.pi fun _ : ι ↦ 𝓘(ℝ)) g y (v 0) =
      ((v 0 : (ι → ℝ) × (ι → ℝ)).1 :
        TangentSpace (ModelWithCorners.pi fun _ : ι ↦ 𝓘(ℝ)) (g y)) :=
    DFunLike.congr_fun (((AddCircle.hasMFDerivAt_pi_coe p y.1).comp y
      (ContinuousLinearMap.fst ℝ (ι → ℝ) (ι → ℝ)).hasMFDerivAt).mfderiv) (v 0)
  exact (DFunLike.congr_arg (torusCover p y).2 hg).trans
    (torusCover_snd_apply p y (v 0 : (ι → ℝ) × (ι → ℝ)).1)

/-- **Action–angle formula for the Liouville form.** Pulling `liouvilleForm` back along
`torusTrivializationDiffeomorph` gives `∑ i, c i * a i` on `(a, b)` at `(θ, c)`. -/
theorem mpullback_torusTrivializationDiffeomorph_liouvilleForm_apply [DecidableEq ι]
    (q : (∀ i, AddCircle (p i)) × (ι → ℝ)) (a b : ι → ℝ) :
    (SmoothForm.mpullback (torusTrivializationDiffeomorph p)
        (torusTrivializationDiffeomorph p).contMDiff
        (liouvilleForm (ModelWithCorners.pi fun _ : ι ↦ 𝓘(ℝ)) (∀ i, AddCircle (p i)))).1 q
        ![(Manifold.tangentSpaceProdEquiv q).symm (a, b)] =
      ∑ i, q.2 i * a i := by
  rw [SmoothForm.coe_mpullback,
    mpullback_liouvilleForm_apply_of_proj_comp_eq (g := Prod.fst) (fun _ ↦ rfl)
      ((torusTrivializationDiffeomorph p).contMDiff q |>.mdifferentiableAt (by simp))]
  have hq : mfderiv ((ModelWithCorners.pi fun _ : ι ↦ 𝓘(ℝ)).prod 𝓘(ℝ, ι → ℝ))
      (ModelWithCorners.pi fun _ : ι ↦ 𝓘(ℝ)) Prod.fst q
      (![(Manifold.tangentSpaceProdEquiv q).symm (a, b)] 0) =
      (a : TangentSpace (ModelWithCorners.pi fun _ : ι ↦ 𝓘(ℝ)) q.1) := by
    rw [Matrix.cons_val_zero, mfderiv_fst, Manifold.tangentSpaceProdEquiv_symm_apply]
    rfl
  exact (DFunLike.congr_arg (torusTrivializationDiffeomorph p q).2 hq).trans
    (torusTrivializationDiffeomorph_snd_apply p q a)

private def torusCoverModelCLM :
    (ι → ℝ) × (ι → ℝ) →L[ℝ] (ι → ℝ) × ((ι → ℝ) →L[ℝ] ℝ) :=
  (ContinuousLinearMap.id ℝ (ι → ℝ)).prodMap
    (∑ i, ContinuousLinearMap.smulRightL ℝ (ι → ℝ) ((ι → ℝ) →L[ℝ] ℝ)
      (ContinuousLinearMap.proj (R := ℝ) (φ := fun _ : ι ↦ ℝ) i)
      (ContinuousLinearMap.proj (R := ℝ) (φ := fun _ : ι ↦ ℝ) i))

private theorem torusCoverModelCLM_fst (y : (ι → ℝ) × (ι → ℝ)) :
    (torusCoverModelCLM y).1 = y.1 := rfl

private theorem torusCoverModelCLM_snd_apply (y : (ι → ℝ) × (ι → ℝ)) (w : ι → ℝ) :
    (torusCoverModelCLM y).2 w = ∑ i, y.2 i * w i := by
  simp [torusCoverModelCLM]

/-- `torusCover p` pulls the canonical symplectic form of `T*(∀ i, AddCircle (p i))` back to the
standard linear symplectic form `∑ i, (a i * b' i - a' i * b i)`. -/
theorem eval₂_symplecticForm_mfderiv_torusCover (y : (ι → ℝ) × (ι → ℝ)) (a a' b b' : ι → ℝ) :
    SmoothBundleForm.eval₂
        (symplecticForm (ModelWithCorners.pi fun _ : ι ↦ 𝓘(ℝ)) (∀ i, AddCircle (p i)))
        (torusCover p y)
        (mfderiv 𝓘(ℝ, (ι → ℝ) × (ι → ℝ))
          ((ModelWithCorners.pi fun _ : ι ↦ 𝓘(ℝ)).prod 𝓘(ℝ, (ι → ℝ) →L[ℝ] ℝ))
          (torusCover p) y (a, b))
        (mfderiv 𝓘(ℝ, (ι → ℝ) × (ι → ℝ))
          ((ModelWithCorners.pi fun _ : ι ↦ 𝓘(ℝ)).prod 𝓘(ℝ, (ι → ℝ) →L[ℝ] ℝ))
          (torusCover p) y (a', b')) =
      ∑ i, (a i * b' i - a' i * b i) := by
  let L := torusCoverModelCLM (ι := ι)
  let v : TangentSpace 𝓘(ℝ, (ι → ℝ) × (ι → ℝ)) y := (a, b)
  let v' : TangentSpace 𝓘(ℝ, (ι → ℝ) × (ι → ℝ)) y := (a', b')
  change SmoothBundleForm.eval₂
      (symplecticForm (ModelWithCorners.pi fun _ : ι ↦ 𝓘(ℝ)) (∀ i, AddCircle (p i)))
      (torusCover p y)
      (mfderiv 𝓘(ℝ, (ι → ℝ) × (ι → ℝ))
        ((ModelWithCorners.pi fun _ : ι ↦ 𝓘(ℝ)).prod 𝓘(ℝ, (ι → ℝ) →L[ℝ] ℝ)) (torusCover p) y v)
      (mfderiv 𝓘(ℝ, (ι → ℝ) × (ι → ℝ))
        ((ModelWithCorners.pi fun _ : ι ↦ 𝓘(ℝ)).prod 𝓘(ℝ, (ι → ℝ) →L[ℝ] ℝ))
        (torusCover p) y v') =
    ∑ i, (a i * b' i - a' i * b i)
  rw [← SmoothForm.eval₂_mpullback (I := 𝓘(ℝ, (ι → ℝ) × (ι → ℝ))) (torusCover p)
      (contMDiff_torusCover p),
    SmoothBundleForm.eval₂_apply, symplecticForm_eq_neg_mextDerivₗ, map_neg,
    ← SmoothForm.mextDerivₗ_mpullback, NegMemClass.coe_neg, mextDerivₗ_apply, Pi.neg_apply,
    ContinuousAlternatingMap.neg_apply]
  have hliouv : (SmoothForm.mpullback (I := 𝓘(ℝ, (ι → ℝ) × (ι → ℝ))) (torusCover p)
      (contMDiff_torusCover p)
      (liouvilleForm (ModelWithCorners.pi fun _ : ι ↦ 𝓘(ℝ)) (∀ i, AddCircle (p i)))).1 =
      fun z ↦ (cotangentLiouvilleForm (L z)).compContinuousLinearMap (fderiv ℝ L z) := by
    funext z
    ext w
    let w' : Fin 1 → (ι → ℝ) × (ι → ℝ) := w
    refine (mpullback_torusCover_liouvilleForm_apply p z w).trans ?_
    change ∑ i, z.2 i * (w' 0).1 i =
      ((cotangentLiouvilleForm (L z)).compContinuousLinearMap (fderiv ℝ L z)) w'
    rw [ContinuousAlternatingMap.compContinuousLinearMap_apply, L.fderiv,
      cotangentLiouvilleForm_apply]
    simp [L, torusCoverModelCLM_fst, torusCoverModelCLM_snd_apply]
  have hd : mextDeriv (SmoothForm.mpullback (I := 𝓘(ℝ, (ι → ℝ) × (ι → ℝ))) (torusCover p)
        (contMDiff_torusCover p)
        (liouvilleForm (ModelWithCorners.pi fun _ : ι ↦ 𝓘(ℝ)) (∀ i, AddCircle (p i)))).1 y =
      extDeriv (fun z ↦ (cotangentLiouvilleForm (L z)).compContinuousLinearMap (fderiv ℝ L z))
        y :=
    (mextDeriv_eq_extDeriv _ y).trans (congrFun (congrArg extDeriv hliouv) y)
  rw [hd, extDeriv_pullback (differentiableAt_cotangentLiouvilleForm (L y))
      ((L.contDiff (n := ∞)).contDiffAt) (by simp)]
  let u : Fin 2 → (ι → ℝ) × (ι → ℝ) := ![(a, b), (a', b')]
  change -((extDeriv cotangentLiouvilleForm (L y)).compContinuousLinearMap (fderiv ℝ L y)) u =
    ∑ i, (a i * b' i - a' i * b i)
  rw [ContinuousAlternatingMap.compContinuousLinearMap_apply, L.fderiv,
    neg_extDeriv_cotangentLiouvilleForm_apply]
  simp only [u, Function.comp_apply, Matrix.cons_val_zero, Matrix.cons_val_one,
    strongDualCotangentSymplecticForm_apply, L, torusCoverModelCLM_fst,
    torusCoverModelCLM_snd_apply, ← Finset.sum_sub_distrib]
  exact Finset.sum_congr rfl fun i _ ↦ by ring

/-- **Action–angle formula for the canonical symplectic form.** Pulling `symplecticForm` back along
`torusTrivializationDiffeomorph` gives `∑ i, (a i * b' i - a' i * b i)`, that is `∑ i, dθ_i ∧ dI_i`,
at `(θ, c)`. -/
theorem eval₂_mpullback_torusTrivializationDiffeomorph_symplecticForm [DecidableEq ι]
    (q : (∀ i, AddCircle (p i)) × (ι → ℝ)) (a a' b b' : ι → ℝ) :
    SmoothBundleForm.eval₂
        (SmoothForm.mpullback (torusTrivializationDiffeomorph p)
          (torusTrivializationDiffeomorph p).contMDiff
          (symplecticForm (ModelWithCorners.pi fun _ : ι ↦ 𝓘(ℝ)) (∀ i, AddCircle (p i))))
        q ((Manifold.tangentSpaceProdEquiv q).symm (a, b))
        ((Manifold.tangentSpaceProdEquiv q).symm (a', b')) =
      ∑ i, (a i * b' i - a' i * b i) := by
  obtain ⟨θ, c⟩ := q
  obtain ⟨ϑ, hϑ⟩ := AddCircle.pi_coe_surjective p θ
  subst hϑ
  let cov : (ι → ℝ) × (ι → ℝ) → (∀ i, AddCircle (p i)) × (ι → ℝ) :=
    Prod.map (fun t : ι → ℝ ↦ fun i ↦ (t i : AddCircle (p i))) id
  have hmd : ∀ u v : ι → ℝ,
      mfderiv ((ModelWithCorners.pi fun _ : ι ↦ 𝓘(ℝ)).prod 𝓘(ℝ, ι → ℝ))
        ((ModelWithCorners.pi fun _ : ι ↦ 𝓘(ℝ)).prod 𝓘(ℝ, (ι → ℝ) →L[ℝ] ℝ))
        (torusTrivializationDiffeomorph p) (cov (ϑ, c))
        ((Manifold.tangentSpaceProdEquiv (cov (ϑ, c))).symm (u, v)) =
      mfderiv 𝓘(ℝ, (ι → ℝ) × (ι → ℝ))
        ((ModelWithCorners.pi fun _ : ι ↦ 𝓘(ℝ)).prod 𝓘(ℝ, (ι → ℝ) →L[ℝ] ℝ))
        (torusCover p) (ϑ, c) (u, v) := fun u v ↦ by
    let w : TangentSpace 𝓘(ℝ, (ι → ℝ) × (ι → ℝ)) (ϑ, c) := (u, v)
    have hcov : mfderiv 𝓘(ℝ, (ι → ℝ) × (ι → ℝ))
        ((ModelWithCorners.pi fun _ : ι ↦ 𝓘(ℝ)).prod 𝓘(ℝ, ι → ℝ)) cov (ϑ, c) w =
        (Manifold.tangentSpaceProdEquiv (cov (ϑ, c))).symm (u, v) := by
      rw [modelWithCornersSelf_prod, ← chartedSpaceSelf_prod,
        mfderiv_prodMap (AddCircle.hasMFDerivAt_pi_coe p ϑ).mdifferentiableAt mdifferentiableAt_id,
        AddCircle.mfderiv_pi_coe, mfderiv_id]
      exact (Manifold.tangentSpaceProdEquiv_symm_apply _ _).symm
    have hdiff : MDifferentiableAt 𝓘(ℝ, (ι → ℝ) × (ι → ℝ))
        ((ModelWithCorners.pi fun _ : ι ↦ 𝓘(ℝ)).prod 𝓘(ℝ, ι → ℝ)) cov (ϑ, c) := by
      rw [modelWithCornersSelf_prod, ← chartedSpaceSelf_prod]
      exact (AddCircle.hasMFDerivAt_pi_coe p ϑ).mdifferentiableAt.prodMap mdifferentiableAt_id
    exact (DFunLike.congr_arg _ hcov.symm).trans
      ((mfderiv_comp_apply (ϑ, c)
        ((torusTrivializationDiffeomorph p).contMDiff _ |>.mdifferentiableAt (by simp)) hdiff
        w).symm)
  change SmoothBundleForm.eval₂
      (SmoothForm.mpullback (torusTrivializationDiffeomorph p)
        (torusTrivializationDiffeomorph p).contMDiff
        (symplecticForm (ModelWithCorners.pi fun _ : ι ↦ 𝓘(ℝ)) (∀ i, AddCircle (p i))))
      (cov (ϑ, c))
      ((Manifold.tangentSpaceProdEquiv (cov (ϑ, c))).symm (a, b))
      ((Manifold.tangentSpaceProdEquiv (cov (ϑ, c))).symm (a', b')) = _
  rw [SmoothForm.eval₂_mpullback, hmd a b, hmd a' b']
  exact eval₂_symplecticForm_mfderiv_torusCover p (ϑ, c) a a' b b'

end Trivialization


/-! ### Lagrangian sections of constant-coefficient angle forms -/

/-- **The graph of a constant-coefficient angle form is Lagrangian.** For every `c : ι → ℝ`, the
section of the cotangent bundle of the torus defined by the closed one-form `∑ j, c j • dt_j` is a
Lagrangian map for the canonical symplectic form. -/
theorem isLagrangianMap_section_sum_smul_torusTimeForm (c : ι → ℝ) :
    (isSymplectic_symplecticForm (I := ModelWithCorners.pi fun _ : ι ↦ 𝓘(ℝ))
        (M := ∀ i, AddCircle (p i))).isNondegenerate.IsLagrangianMap
      (ModelWithCorners.pi fun _ : ι ↦ 𝓘(ℝ))
      (fun x ↦ TotalSpace.mk' ((ι → ℝ) →L[ℝ] ℝ) x
        (SmoothForm.degreeOneEquiv (∑ j, c j • torusTimeForm p j) x)) := by
  exact (isLagrangianMap_section_iff _).2 (isClosed_sum_smul_torusTimeForm p c)

/-- **The graph of a constant-coefficient angle form is exact only when it is the zero section.**
The section of the cotangent bundle of the torus defined by `∑ j, c j • dt_j` is an exact
Lagrangian map, for the primitive `λ` of `ω = -dλ` and some primitive on the torus, if and only if
`c = 0`. -/
theorem exists_isExactLagrangianMap_section_sum_smul_torusTimeForm_iff (c : ι → ℝ) :
    (∃ h : (∀ i, AddCircle (p i)) → ℝ,
      (isSymplectic_symplecticForm (I := ModelWithCorners.pi fun _ : ι ↦ 𝓘(ℝ))
          (M := ∀ i, AddCircle (p i))).isNondegenerate.IsExactLagrangianMap
        (ModelWithCorners.pi fun _ : ι ↦ 𝓘(ℝ)) (liouvilleForm _ _)
        (fun x ↦ TotalSpace.mk' ((ι → ℝ) →L[ℝ] ℝ) x
          (SmoothForm.degreeOneEquiv (∑ j, c j • torusTimeForm p j) x)) h) ↔
      c = 0 := by
  rw [exists_isExactLagrangianMap_section_iff, sum_smul_torusTimeForm_mem_exactForms_iff]

/-- **A nonzero constant-coefficient angle form has graph disjoint from the zero section.** At
every point `x` of the torus, the section of the cotangent bundle defined by `∑ j, c j • dt_j`
meets the zero section if and only if `c = 0`. -/
theorem section_sum_smul_torusTimeForm_eq_zeroSection_iff (c : ι → ℝ)
    (x : ∀ i, AddCircle (p i)) :
    TotalSpace.mk' ((ι → ℝ) →L[ℝ] ℝ) x
        (SmoothForm.degreeOneEquiv (∑ j, c j • torusTimeForm p j) x) =
      zeroSection ((ι → ℝ) →L[ℝ] ℝ)
        (fun y : ∀ i, AddCircle (p i) ↦
          TangentSpace (ModelWithCorners.pi fun _ : ι ↦ 𝓘(ℝ)) y →L[ℝ] ℝ) x ↔
      c = 0 := by
  classical
  rw [zeroSection, TotalSpace.mk_inj]
  refine ⟨fun h ↦ funext fun i ↦ ?_, fun h ↦ ?_⟩
  · -- The form sends every tangent vector `v` to `∑ j, c j * v j`; evaluate on the `i`-th
    -- coordinate vector.
    have hv (v : TangentSpace (ModelWithCorners.pi fun _ : ι ↦ 𝓘(ℝ)) x) :
        ∑ j, c j * v j = 0 := by
      have hx := SmoothForm.degreeOneEquiv_apply_apply (∑ j, c j • torusTimeForm p j) x v
      rw [h, sum_smul_torusTimeForm_apply, zero_apply] at hx
      exact hx.symm
    simpa [Pi.single_apply] using hv (Pi.single i 1)
  · ext v
    simp [h]

/-- **The graph of an angle form is Lagrangian.** The section of the cotangent bundle of the torus
defined by the coordinate time form `dt_i` is a Lagrangian map for the canonical symplectic form. -/
theorem isLagrangianMap_section_torusTimeForm (i : ι) :
    (isSymplectic_symplecticForm (I := ModelWithCorners.pi fun _ : ι ↦ 𝓘(ℝ))
        (M := ∀ i, AddCircle (p i))).isNondegenerate.IsLagrangianMap
      (ModelWithCorners.pi fun _ : ι ↦ 𝓘(ℝ))
      (fun x ↦ TotalSpace.mk' ((ι → ℝ) →L[ℝ] ℝ) x
        (SmoothForm.degreeOneEquiv (torusTimeForm p i) x)) :=
  (isLagrangianMap_section_iff _).2 (isClosed_torusTimeForm p i)

/-- **The graph of an angle form is not exact.** The section of the cotangent bundle of the torus
defined by the coordinate time form `dt_i` is not an exact Lagrangian map for the primitive `λ` of
`ω = -dλ`, whatever primitive on the torus is chosen. -/
@[simp]
theorem not_exists_isExactLagrangianMap_section_torusTimeForm (i : ι) :
    ¬∃ h : (∀ i, AddCircle (p i)) → ℝ,
      (isSymplectic_symplecticForm (I := ModelWithCorners.pi fun _ : ι ↦ 𝓘(ℝ))
          (M := ∀ i, AddCircle (p i))).isNondegenerate.IsExactLagrangianMap
        (ModelWithCorners.pi fun _ : ι ↦ 𝓘(ℝ)) (liouvilleForm _ _)
        (fun x ↦ TotalSpace.mk' ((ι → ℝ) →L[ℝ] ℝ) x
          (SmoothForm.degreeOneEquiv (torusTimeForm p i) x)) h := by
  rw [exists_isExactLagrangianMap_section_iff]
  exact torusTimeForm_notMem_exactForms p i

end CotangentBundle

end TauCeti
