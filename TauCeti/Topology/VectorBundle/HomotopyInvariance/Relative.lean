/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import Mathlib.Analysis.Complex.Tietze
public import TauCeti.Topology.VectorBundle.HomotopyInvariance.Basic
import TauCeti.Topology.Algebra.Module.ContinuousLinearMap.Invertible
import TauCeti.Topology.FiberBundle.Pullback
import TauCeti.Topology.Homotopy.Cylinder.Neighborhood
import TauCeti.Topology.VectorBundle.Extension

/-!
# Relative homotopy invariance of vector bundles over paracompact bases

When the model endomorphism space `F →L[𝕜] F` has the Tietze extension property (in particular for
every finite-rank real or complex vector bundle) and `X` is a paracompact R₁ space, a cylinder
identification already specified over `s × I` for a closed subset `s ⊆ X` and equal to the
identity on `s × {0}` extends to all of `X × I`
(`TauCeti.exists_continuousLinearEquiv_cylinder_of_isClosed` and the finite-rank total-space version
`TauCeti.exists_continuousLinearEquiv_cylinder_of_isClosed_of_continuous`). Applied to a homotopy
relative to `s`, this yields pullback bundle equivalences along homotopic-rel-`s` maps that are
the identity over `s` (`ContinuousMap.HomotopicRel.exists_continuousLinearEquiv_pullback`).

Given `Φ₀` over `s × I` equal to the identity at time `0`, composing `(Ψ₁ (x, t))⁻¹ ∘ Φ₀ (x, t)`
on `s × I` with the identity on `X × {0}` defines a continuous invertible endomorphism of the
zero-slice pullback bundle on the closed union `(s ×ˢ univ) ∪ (univ ×ˢ {0})`. Tietze section
extension (`TauCeti.exists_continuous_section_extension`) extends it to `X × I`, invertible on an
open neighbourhood `W`. By the generalized tube lemma on compact `I` and Urysohn's lemma on normal
`X`, `TauCeti.exists_continuousMap_cylinder_compression` maps `X × I` into `W` via
`(x, t) ↦ (x, ρ x * t)` while fixing `(s ×ˢ univ) ∪ (univ ×ˢ {0})`.

## References

* A. Hatcher, *Vector Bundles and K-Theory*, §1.2, Proposition 1.7, for relative cylinder extension
  and relative homotopy invariance of pullbacks over paracompact bases.
* M. F. Atiyah, *K-Theory*, §1.4, Lemma 1.4.3, for extension of bundle isomorphisms from closed
  subsets.
-/

public section

open Bundle FiberBundle Set Function ContinuousLinearMap
open scoped Topology unitInterval

namespace TauCeti

section RelativeCylinder

universe u v w

private theorem transport_beta_eq {𝕜 X : Type*} [Semiring 𝕜] [TopologicalSpace X]
    {E : X × I → Type*} [∀ q, AddCommMonoid (E q)] [∀ q, Module 𝕜 (E q)]
    [∀ q, TopologicalSpace (E q)] {q q' : X × I} (hq : q' = q)
    (h0 : cylinderZero X q' = cylinderZero X q)
    (β : ∀ p : X × I, ((cylinderZero X : X × I → X × I) *ᵖ E) p →L[𝕜]
      ((cylinderZero X : X × I → X × I) *ᵖ E) p) :
    (show E (cylinderZero X q) →L[𝕜] E (cylinderZero X q) from h0 ▸ β q') = β q := by
  cases hq
  rfl

section General

variable {𝕜 : Type v} [NontriviallyNormedField 𝕜] [NormedAlgebra ℝ 𝕜]
  {X : Type u} [TopologicalSpace X]
  {F : Type w} [NormedAddCommGroup F] [NormedSpace 𝕜 F]
  {E : X × I → Type*} [∀ q, AddCommGroup (E q)] [∀ q, Module 𝕜 (E q)]
  [∀ q, TopologicalSpace (E q)] [TopologicalSpace (TotalSpace F E)]
  [FiberBundle F E] [VectorBundle 𝕜 F E]
  [∀ q, IsTopologicalAddGroup (E q)] [∀ q, ContinuousSMul 𝕜 (E q)]

omit [NormedAlgebra ℝ 𝕜] in
/-- Compatibility on `(s ×ˢ univ) ∪ (univ ×ˢ {0})` of the partial transition endomorphism
`(Ψ₁ q)⁻¹ ∘ Φ₀ q` over `s × I` and the identity over `X × {0}`. -/
private theorem continuousOn_transition_union [CompleteSpace F] {s : Set X} (hs : IsClosed s)
    {Ψ₁ : ∀ q : X × I, E (q.1, 0) ≃L[𝕜] E q}
    (hΨ₁ : Continuous fun q : X × I ↦ TotalSpace.mk' (F →L[𝕜] F)
      (E := fun z : X × I ↦ ((cylinderZero X : X × I → X × I) *ᵖ E) z →L[𝕜] E z)
      q (Ψ₁ q : E (q.1, 0) →L[𝕜] E q))
    {Φ₀ : ∀ q : s × I, E (q.1.val, 0) ≃L[𝕜] E (q.1.val, q.2)}
    (hΦ₀ : Continuous fun q : s × I ↦ TotalSpace.mk' (F →L[𝕜] F)
      (E := fun z : X × I ↦ ((cylinderZero X : X × I → X × I) *ᵖ E) z →L[𝕜] E z)
      (cylinderSetIncl s q) (Φ₀ q : E (q.1.val, 0) →L[𝕜] E (q.1.val, q.2)))
    {α : ∀ q : X × I,
      ((cylinderZero X : X × I → X × I) *ᵖ E) q →L[𝕜]
      ((cylinderZero X : X × I → X × I) *ᵖ E) q}
    (hαs : ∀ (x : s) (t : I), α (x.val, t) =
      ((Ψ₁ (x.val, t)).symm : E (x.val, t) →L[𝕜] E (x.val, 0)).comp
        (Φ₀ (x, t) : E (x.val, 0) →L[𝕜] E (x.val, t)))
    (hα0 : ∀ x : X, α (x, 0) = ContinuousLinearMap.id 𝕜 (E (x, 0))) :
    ContinuousOn (fun q : X × I ↦ TotalSpace.mk' (F →L[𝕜] F)
      (E := fun z : X × I ↦
        ((cylinderZero X : X × I → X × I) *ᵖ E) z →L[𝕜]
        ((cylinderZero X : X × I → X × I) *ᵖ E) z) q (α q))
      ((s ×ˢ (univ : Set I)) ∪ ((univ : Set X) ×ˢ {(0 : I)})) := by
  have hΨi : Continuous fun q : X × I ↦ TotalSpace.mk' (F →L[𝕜] F)
      (E := fun z : X × I ↦ E z →L[𝕜] ((cylinderZero X : X × I → X × I) *ᵖ E) z) q
      ((Ψ₁ q).symm : E q →L[𝕜] E (q.1, 0)) :=
    (Continuous.clm_bundle_inverse (E₁ := (cylinderZero X : X × I → X × I) *ᵖ E) (E₂ := E)
      (b := id) hΨ₁ (fun q ↦ ⟨Ψ₁ q, rfl⟩)).congr fun q ↦
      congrArg (TotalSpace.mk' (F →L[𝕜] F) q) (inverse_equiv (Ψ₁ q))
  have hcomp : Continuous fun q : s × I ↦ TotalSpace.mk' (F →L[𝕜] F)
      (E := fun z : X × I ↦
        ((cylinderZero X : X × I → X × I) *ᵖ E) z →L[𝕜]
        ((cylinderZero X : X × I → X × I) *ᵖ E) z) (cylinderSetIncl s q)
      (((Ψ₁ (q.1.val, q.2)).symm : E (q.1.val, q.2) →L[𝕜] E (q.1.val, 0)).comp
        (Φ₀ q : E (q.1.val, 0) →L[𝕜] E (q.1.val, q.2))) :=
    Continuous.clm_bundle_comp (E₁ := (cylinderZero X : X × I → X × I) *ᵖ E) (E₂ := E)
      (E₃ := (cylinderZero X : X × I → X × I) *ᵖ E) (b := cylinderSetIncl s)
      (hΨi.comp (cylinderSetIncl s).continuous) hΦ₀
  refine ContinuousOn.union_of_isClosed ?_ ?_ (hs.prod isClosed_univ)
    (isClosed_univ.prod isClosed_singleton)
  · rw [continuousOn_iff_continuous_domRestrict]
    refine (hcomp.comp (((continuous_fst.comp continuous_subtypeVal).subtype_mk
      (fun q ↦ q.property.1)).prodMk (continuous_snd.comp continuous_subtypeVal))).congr
      fun q ↦ ?_
    exact congrArg (TotalSpace.mk' (F →L[𝕜] F) q.val)
      (hαs ⟨q.val.1, q.property.1⟩ q.val.2).symm
  · refine (continuous_hom_bundle_id
        (E := (cylinderZero X : X × I → X × I) *ᵖ E)).continuousOn.congr fun q hq ↦ ?_
    obtain ⟨x, t⟩ := q
    obtain ⟨_, rfl⟩ : x ∈ (univ : Set X) ∧ t = 0 := hq
    exact congrArg (TotalSpace.mk' (F →L[𝕜] F) (x, 0)) (hα0 x)

variable [R1Space X] [ParacompactSpace X]

/-- Extend the partial transition `(Ψ₁ q)⁻¹ ∘ Φ₀ q` from `(s ×ˢ univ) ∪ (univ ×ˢ {0})` to a
continuous invertible zero-slice endomorphism `γ` over `X × I` by Tietze extension followed by a
tube-lemma cylinder compression into the invertible locus. -/
private theorem exists_compressed_transition_equiv [CompleteSpace F]
    [TietzeExtension.{u, w} (F →L[𝕜] F)] {s : Set X} (hs : IsClosed s)
    {Ψ₁ : ∀ q : X × I, E (q.1, 0) ≃L[𝕜] E q}
    (hΨ₁ : Continuous fun q : X × I ↦ TotalSpace.mk' (F →L[𝕜] F)
      (E := fun z : X × I ↦ ((cylinderZero X : X × I → X × I) *ᵖ E) z →L[𝕜] E z)
      q (Ψ₁ q : E (q.1, 0) →L[𝕜] E q))
    (hΨ₁0 : ∀ x : X, Ψ₁ (x, 0) = ContinuousLinearEquiv.refl 𝕜 (E (x, 0)))
    (Φ₀ : ∀ q : s × I, E (q.1.val, 0) ≃L[𝕜] E (q.1.val, q.2))
    (hΦ₀ : Continuous fun q : s × I ↦ TotalSpace.mk' (F →L[𝕜] F)
      (E := fun z : X × I ↦ ((cylinderZero X : X × I → X × I) *ᵖ E) z →L[𝕜] E z)
      (cylinderSetIncl s q) (Φ₀ q : E (q.1.val, 0) →L[𝕜] E (q.1.val, q.2)))
    (hΦ₀0 : ∀ x : s, Φ₀ (x, 0) = ContinuousLinearEquiv.refl 𝕜 (E (x.val, 0))) :
    ∃ γ : ∀ q : X × I, E (q.1, 0) ≃L[𝕜] E (q.1, 0),
      Continuous (fun q : X × I ↦ TotalSpace.mk' (F →L[𝕜] F)
        (E := fun z : X × I ↦
          ((cylinderZero X : X × I → X × I) *ᵖ E) z →L[𝕜]
          ((cylinderZero X : X × I → X × I) *ᵖ E) z)
        q (γ q : E (q.1, 0) →L[𝕜] E (q.1, 0))) ∧
      (∀ x : X, γ (x, 0) = ContinuousLinearEquiv.refl 𝕜 (E (x, 0))) ∧
      ∀ (x : s) (t : I), γ (x.val, t) = (Φ₀ (x, t)).trans (Ψ₁ (x.val, t)).symm := by
  classical
  let α : ∀ q : X × I,
      ((cylinderZero X : X × I → X × I) *ᵖ E) q →L[𝕜]
      ((cylinderZero X : X × I → X × I) *ᵖ E) q := fun q ↦
    if hq : q.1 ∈ s then
      ((Ψ₁ q).symm : E q →L[𝕜] E (q.1, 0)).comp (Φ₀ (⟨q.1, hq⟩, q.2) : E (q.1, 0) →L[𝕜] E q)
    else ContinuousLinearMap.id 𝕜 (E (q.1, 0))
  have hα0 (x : X) : α (x, 0) = ContinuousLinearMap.id 𝕜 (E (x, 0)) := by
    by_cases hx : x ∈ s <;> simp [α, hx, hΨ₁0, hΦ₀0] <;> rfl
  have : ∀ z : X × I, @ContinuousConstSMul 𝕜 (((cylinderZero X : X × I → X × I) *ᵖ E) z) _
      (inferInstance : Module 𝕜 (((cylinderZero X : X × I → X × I) *ᵖ E) z)).toSMul := fun z ↦
    @ContinuousSMul.continuousConstSMul _ _ _ _ _
      (Bundle.Pullback.instContinuousSMul (⇑(cylinderZero X)) z)
  obtain ⟨β, hβ, hβα⟩ := exists_continuous_section_extension 𝕜
    (F := F →L[𝕜] F)
    (E := fun z : X × I ↦
      ((cylinderZero X : X × I → X × I) *ᵖ E) z →L[𝕜]
      ((cylinderZero X : X × I → X × I) *ᵖ E) z)
    ((hs.prod isClosed_univ).union (isClosed_univ.prod isClosed_singleton))
    (continuousOn_transition_union hs hΨ₁ hΦ₀
      (α := α) (fun x t ↦ by simp only [α, x.property, ↓reduceDIte]; rfl) hα0)
  obtain ⟨r, hr₁, hrW, hr0, hrs⟩ := exists_continuousMap_cylinder_compression hs
    hβ.isOpen_setOf_clm_bundle_isInvertible
    (fun q hq ↦ by
      rw [mem_ofPred_eq, hβα q (Or.inl hq)]
      simp only [α, hq.1, ↓reduceDIte]
      exact ⟨(Φ₀ (⟨q.1, hq.1⟩, q.2)).trans (Ψ₁ q).symm, rfl⟩)
    (fun ⟨x, t⟩ ⟨hx, ht⟩ ↦ by
      obtain rfl : t = 0 := ht
      rw [mem_ofPred_eq, hβα (x, 0) (Or.inr ⟨hx, rfl⟩), hα0]
      exact ⟨ContinuousLinearEquiv.refl 𝕜 _, rfl⟩)
  let h0 (q : X × I) : cylinderZero X (r q) = cylinderZero X q := Prod.ext (hr₁ q) rfl
  choose γ hγ using fun q : X × I ↦
    ContinuousLinearMap.IsInvertible.transport (V := E) (W := E) (h0 q) (h0 q) (hrW q)
  have htr {a b : X × I} (h : a = b) (T : E a →L[𝕜] E a) :
      (let f {c d : X × I} (hc : a = c) (hd : a = d) : E c →L[𝕜] E d := hc ▸ hd ▸ T
       f h h) = (show E b →L[𝕜] E b from h ▸ T) := by
    cases h
    rfl
  have hγ' (q : X × I) : (γ q : E (cylinderZero X q) →L[𝕜] E (cylinderZero X q)) =
      (show E (cylinderZero X q) →L[𝕜] E (cylinderZero X q) from h0 q ▸ β (r q)) :=
    (hγ q).trans (htr (h0 q) (β (r q)))
  refine ⟨γ, (continuous_hom_bundle_pullback_comp_of_eq (cylinderZero X) hβ r.continuous
      h0).congr fun q ↦ congrArg (TotalSpace.mk' (F →L[𝕜] F) q) (hγ' q).symm,
    fun x ↦ ?_, fun x t ↦ ?_⟩
  · exact ContinuousLinearEquiv.coe_injective ((hγ' (x, 0)).trans
      ((transport_beta_eq (hr0 x) (h0 (x, 0)) β).trans
        ((hβα (x, 0) (Or.inr ⟨mem_univ x, mem_singleton 0⟩)).trans (hα0 x))))
  · exact ContinuousLinearEquiv.coe_injective ((hγ' (x.val, t)).trans
      ((transport_beta_eq (hrs x.val x.property t) (h0 (x.val, t)) β).trans
        ((hβα (x.val, t) (Or.inl ⟨x.property, mem_univ t⟩)).trans
          (by simp only [α, x.property, ↓reduceDIte]; rfl))))

/-- **Relative homotopy invariance of vector bundles over a cylinder.** Over a paracompact R₁
base `X`, let `E` be a Banach vector bundle over `X × I` whose model endomorphism space
`F →L[𝕜] F` has the Tietze extension property, and let `s ⊆ X` be closed. Every Hom-bundle
continuous family of fibrewise linear equivalences `Φ₀ (x, t) : E (x, 0) ≃L[𝕜] E (x, t)` over
`s × I` equal to the identity on `s × {0}` extends to a Hom-bundle continuous family
`Φ (x, t) : E (x, 0) ≃L[𝕜] E (x, t)` over `X × I`, continuous on total spaces together with its
inverse and equal to the identity on `X × {0}`. -/
theorem exists_continuousLinearEquiv_cylinder_of_isClosed [CompleteSpace F]
    [TietzeExtension.{u, w} (F →L[𝕜] F)] {s : Set X} (hs : IsClosed s)
    (Φ₀ : ∀ q : s × I, E (q.1.val, 0) ≃L[𝕜] E (q.1.val, q.2))
    (hΦ₀ : Continuous fun q : s × I ↦ TotalSpace.mk' (F →L[𝕜] F)
      (E := fun z : X × I ↦ ((cylinderZero X : X × I → X × I) *ᵖ E) z →L[𝕜] E z)
      (cylinderSetIncl s q) (Φ₀ q : E (q.1.val, 0) →L[𝕜] E (q.1.val, q.2)))
    (hΦ₀0 : ∀ x : s, Φ₀ (x, 0) = ContinuousLinearEquiv.refl 𝕜 (E (x.val, 0))) :
    ∃ Φ : ∀ q : X × I, E (q.1, 0) ≃L[𝕜] E q,
      Continuous (fun q : X × I ↦ TotalSpace.mk' (F →L[𝕜] F)
        (E := fun z : X × I ↦ ((cylinderZero X : X × I → X × I) *ᵖ E) z →L[𝕜] E z)
        q (Φ q : E (q.1, 0) →L[𝕜] E q)) ∧
      Continuous (fun v : TotalSpace F ((cylinderZero X : X × I → X × I) *ᵖ E) ↦
        TotalSpace.mk' F v.proj (Φ v.proj v.snd)) ∧
      Continuous (fun v : TotalSpace F E ↦ TotalSpace.mk' F
        (E := (cylinderZero X : X × I → X × I) *ᵖ E) v.proj ((Φ v.proj).symm v.snd)) ∧
      (∀ x, Φ (x, 0) = ContinuousLinearEquiv.refl 𝕜 (E (x, 0))) ∧
      ∀ (x : s) (t : I), Φ (x.val, t) = Φ₀ (x, t) := by
  obtain ⟨Ψ₁, hΨ₁, hΨ₁0⟩ := exists_continuous_hom_bundle_cylinder (𝕜 := 𝕜) (F := F) (E := E)
  obtain ⟨γ, hγc, hγ0, hγs⟩ := exists_compressed_transition_equiv hs hΨ₁ hΨ₁0 Φ₀ hΦ₀ hΦ₀0
  let Φ : ∀ q : X × I, E (q.1, 0) ≃L[𝕜] E q := fun q ↦ (γ q).trans (Ψ₁ q)
  have hΦhom : Continuous fun q : X × I ↦ TotalSpace.mk' (F →L[𝕜] F)
      (E := fun z : X × I ↦ ((cylinderZero X : X × I → X × I) *ᵖ E) z →L[𝕜] E z) q
      (Φ q : E (q.1, 0) →L[𝕜] E q) :=
    (Continuous.clm_bundle_comp (E₁ := (cylinderZero X : X × I → X × I) *ᵖ E)
      (E₂ := (cylinderZero X : X × I → X × I) *ᵖ E) (E₃ := E) (b := id)
      hΨ₁ hγc).congr fun _ ↦ rfl
  obtain ⟨hfwd, hinv⟩ :=
    continuous_bundle_of_hom (E₁ := (cylinderZero X : X × I → X × I) *ᵖ E) Φ hΦhom
  refine ⟨Φ, hΦhom, hfwd, hinv, fun x ↦ ?_, fun x t ↦ ?_⟩
  · ext v
    simp [Φ, hγ0 x, hΨ₁0 x]
  · ext v
    simp [Φ, hγs x t]

end General

section FiniteDimensional

variable {𝕜 : Type v} [RCLike 𝕜]
  {X : Type u} [TopologicalSpace X] [R1Space X] [ParacompactSpace X]
  {F : Type w} [NormedAddCommGroup F] [NormedSpace 𝕜 F] [FiniteDimensional 𝕜 F]
  {E : X × I → Type*} [∀ q, AddCommGroup (E q)] [∀ q, Module 𝕜 (E q)]
  [∀ q, TopologicalSpace (E q)] [TopologicalSpace (TotalSpace F E)]
  [FiberBundle F E] [VectorBundle 𝕜 F E]
  [∀ q, IsTopologicalAddGroup (E q)] [∀ q, ContinuousSMul 𝕜 (E q)]

/-- **Finite-rank relative cylinder theorem.** For a finite-rank real or complex vector bundle `E`
over `X × I` with `X` paracompact and R₁, a family of fibrewise continuous linear equivalences
`Φ₀ (x, t) : E (x, 0) ≃L[𝕜] E (x, t)` over `s × I` (`s ⊆ X` closed) which is continuous on total
spaces and equal to the identity on `s × {0}` extends to a global cylinder trivialization `Φ` over
`X × I`, continuous on total spaces together with its inverse. -/
theorem exists_continuousLinearEquiv_cylinder_of_isClosed_of_continuous {s : Set X}
    (hs : IsClosed s) (Φ₀ : ∀ q : s × I, E (q.1.val, 0) ≃L[𝕜] E (q.1.val, q.2))
    (hΦ₀ : Continuous fun v :
        TotalSpace F ((((cylinderZero X).comp (cylinderSetIncl s) : s × I → X × I)) *ᵖ E) ↦
      TotalSpace.mk' F (E := (cylinderSetIncl s : s × I → X × I) *ᵖ E) v.proj (Φ₀ v.proj v.snd))
    (hΦ₀0 : ∀ x : s, Φ₀ (x, 0) = ContinuousLinearEquiv.refl 𝕜 (E (x.val, 0))) :
    ∃ Φ : ∀ q : X × I, E (q.1, 0) ≃L[𝕜] E q,
      Continuous (fun v : TotalSpace F ((cylinderZero X : X × I → X × I) *ᵖ E) ↦
        TotalSpace.mk' F v.proj (Φ v.proj v.snd)) ∧
      Continuous (fun v : TotalSpace F E ↦ TotalSpace.mk' F
        (E := (cylinderZero X : X × I → X × I) *ᵖ E) v.proj ((Φ v.proj).symm v.snd)) ∧
      (∀ x, Φ (x, 0) = ContinuousLinearEquiv.refl 𝕜 (E (x, 0))) ∧
      ∀ (x : s) (t : I), Φ (x.val, t) = Φ₀ (x, t) := by
  have := FiniteDimensional.completeSpace 𝕜 F
  have hhom := (continuous_hom_bundle_iff (F₁ := F) (F₂ := F)
    (E₁ := (((cylinderZero X).comp (cylinderSetIncl s) : s × I → X × I) *ᵖ E))
    (E₂ := ((cylinderSetIncl s : s × I → X × I) *ᵖ E))
    (fun q : s × I ↦ (Φ₀ q : E (q.1.val, 0) →L[𝕜] E (q.1.val, q.2)))).2 hΦ₀
  have hΦ₀' :=
    (continuous_hom_bundle_pullback_left_comp_iff (cylinderZero X) (cylinderSetIncl s)
      (fun q : s × I ↦ (Φ₀ q : E (q.1.val, 0) →L[𝕜] E (q.1.val, q.2)))).2 hhom
  obtain ⟨Φ, -, hfwd, hinv, h0, hs'⟩ :=
    exists_continuousLinearEquiv_cylinder_of_isClosed hs Φ₀ hΦ₀' hΦ₀0
  exact ⟨Φ, hfwd, hinv, h0, hs'⟩

end FiniteDimensional

end RelativeCylinder

section RelativeHomotopy

universe u v w z

variable {𝕜 : Type v} [NontriviallyNormedField 𝕜] [NormedAlgebra ℝ 𝕜]
  {X : Type u} [TopologicalSpace X] [R1Space X] [ParacompactSpace X]
  {Y : Type z} [TopologicalSpace Y]
  {F : Type w} [NormedAddCommGroup F] [NormedSpace 𝕜 F] [CompleteSpace F]
  [TietzeExtension.{u, w} (F →L[𝕜] F)]
  {E : Y → Type*} [∀ y, AddCommGroup (E y)] [∀ y, Module 𝕜 (E y)]
  [∀ y, TopologicalSpace (E y)] [TopologicalSpace (TotalSpace F E)]
  [FiberBundle F E] [VectorBundle 𝕜 F E]
  [∀ y, IsTopologicalAddGroup (E y)] [∀ y, ContinuousSMul 𝕜 (E y)]

omit [NormedAlgebra ℝ 𝕜] [R1Space X] [ParacompactSpace X] [CompleteSpace F]
  [TietzeExtension.{u, w} (F →L[𝕜] F)] in
/-- Along a homotopy stationary on `s`, transporting each fibre over `(x, t) : s × I` by the
base-point equality `G (x, 0) = G (x, t)` defines a continuous section of the cylinder Hom
bundle. -/
private theorem continuous_hom_bundle_stationary_pullback (G : C(X × I, Y)) {s : Set X}
    (hs : ∀ (x : s) (t : I), G (x.val, 0) = G (x.val, t)) :
    Continuous fun q : s × I ↦ TotalSpace.mk' (F →L[𝕜] F)
      (E := fun z : X × I ↦
        ((cylinderZero X : X × I → X × I) *ᵖ ((G : X × I → Y) *ᵖ E)) z →L[𝕜]
          ((G : X × I → Y) *ᵖ E) z)
      (cylinderSetIncl s q)
      ((hs q.1 q.2 ▸ ContinuousLinearEquiv.refl 𝕜 (E (G (q.1.val, 0))) :
        E (G (q.1.val, 0)) ≃L[𝕜] E (G (q.1.val, q.2))) :
        E (G (q.1.val, 0)) →L[𝕜] E (G (q.1.val, q.2))) := by
  refine continuous_iff_continuousAt.2 fun q₀ ↦ ?_
  refine (continuousAt_hom_bundle_over_pullback_left_iff (cylinderZero X) (cylinderSetIncl s)
    (V := (G : X × I → Y) *ᵖ E) (W' := (G : X × I → Y) *ᵖ E)
    fun q ↦ (((hs q.1 q.2 ▸ ContinuousLinearEquiv.refl 𝕜 (E (G (q.1.val, 0))) :
        E (G (q.1.val, 0)) ≃L[𝕜] E (G (q.1.val, q.2))) :
        E (G (q.1.val, 0)) →L[𝕜] E (G (q.1.val, q.2))) :
        ((cylinderZero X : X × I → X × I) *ᵖ ((G : X × I → Y) *ᵖ E)) (cylinderSetIncl s q) →L[𝕜]
          ((G : X × I → Y) *ᵖ E) (cylinderSetIncl s q))).2 ?_
  refine (continuousAt_inCoordinates_pullback_iff G G
      ((cylinderZero X).continuous.comp (cylinderSetIncl s).continuous).continuousAt
      (cylinderSetIncl s).continuous.continuousAt
      fun q ↦ (((hs q.1 q.2 ▸ ContinuousLinearEquiv.refl 𝕜 (E (G (q.1.val, 0))) :
          E (G (q.1.val, 0)) ≃L[𝕜] E (G (q.1.val, q.2))) :
          E (G (q.1.val, 0)) →L[𝕜] E (G (q.1.val, q.2))) :
          E (G (cylinderZero X (cylinderSetIncl s q))) →L[𝕜]
            E (G (cylinderSetIncl s q)))).2 ?_
  refine (continuousAt_const (y := ContinuousLinearMap.id 𝕜 F)).congr ?_
  have hmem₀ : G (q₀.1.val, 0) ∈ (trivializationAt F E (G (q₀.1.val, 0))).baseSet :=
    mem_baseSet_trivializationAt F E _
  filter_upwards [ContinuousAt.preimage_mem_nhds
      (G.comp ((cylinderZero X).comp (cylinderSetIncl s))).continuous.continuousAt
      ((trivializationAt F E (G (q₀.1.val, 0))).open_baseSet.mem_nhds hmem₀)] with q hq
  exact (ContinuousLinearMap.inCoordinates_transport_refl (hs q₀.1 q₀.2) (hs q.1 q.2) hq).symm

private theorem totalSpace_mk_eq_of_eq {𝕜 Y F : Type*} [Semiring 𝕜]
    {E : Y → Type*} [∀ y, AddCommMonoid (E y)] [∀ y, Module 𝕜 (E y)] [∀ y, TopologicalSpace (E y)]
    {y₀ y₁ : Y} (h : y₀ = y₁) (v : E y₀) :
    (⟨y₁, (h ▸ ContinuousLinearEquiv.refl 𝕜 (E y₀) : E y₀ ≃L[𝕜] E y₁) v⟩ : TotalSpace F E) =
      ⟨y₀, v⟩ := by
  cases h
  rfl

/-- Endpoint form of the relative cylinder theorem along `G : C(X × I, Y)` stationary on `s`. -/
private theorem exists_continuousLinearEquiv_pullback_rel_of_eq (G : C(X × I, Y)) {s : Set X}
    (hs : IsClosed s) {g₀ g₁ : X → Y} (h₀ : ∀ x, G (x, 0) = g₀ x) (h₁ : ∀ x, G (x, 1) = g₁ x)
    (hGs : ∀ x ∈ s, ∀ t : I, G (x, t) = g₀ x) :
    ∃ Φ : ∀ x, E (g₀ x) ≃L[𝕜] E (g₁ x),
      Continuous (fun v : TotalSpace F (g₀ *ᵖ E) ↦
        TotalSpace.mk' F (E := g₁ *ᵖ E) v.proj (Φ v.proj v.snd)) ∧
      Continuous (fun v : TotalSpace F (g₁ *ᵖ E) ↦
        TotalSpace.mk' F (E := g₀ *ᵖ E) v.proj ((Φ v.proj).symm v.snd)) ∧
      ∀ x ∈ s, ∀ v : E (g₀ x), (⟨g₁ x, Φ x v⟩ : TotalSpace F E) = ⟨g₀ x, v⟩ := by
  obtain rfl : g₀ = fun x ↦ G (x, 0) := (funext h₀).symm
  obtain rfl : g₁ = fun x ↦ G (x, 1) := (funext h₁).symm
  have hGs' (x : s) (t : I) : G (x.val, 0) = G (x.val, t) := (hGs x.val x.property t).symm
  obtain ⟨Φ, -, hΦ₁, hΦ₂, -, hΦs⟩ := exists_continuousLinearEquiv_cylinder_of_isClosed
    (𝕜 := 𝕜) (F := F) (E := (G : X × I → Y) *ᵖ E) hs
    (fun q ↦ (hGs' q.1 q.2 ▸ ContinuousLinearEquiv.refl 𝕜 (E (G (q.1.val, 0))) :
      E (G (q.1.val, 0)) ≃L[𝕜] E (G (q.1.val, q.2))))
    (continuous_hom_bundle_stationary_pullback G hGs')
    (fun x ↦ rfl)
  have hs₁ : Continuous fun x : X ↦ (x, (1 : I)) := continuous_id.prodMk continuous_const
  have hps : Continuous ((cylinderZero X : X × I → X × I) ∘ fun x : X ↦ (x, (1 : I))) :=
    (cylinderZero X).continuous.comp hs₁
  refine ⟨fun x ↦ Φ (x, 1),
    Bundle.Pullback.continuous_totalSpaceMap_comp_left
      (E₁ := E) (E₂ := E) (f := (G : X × I → Y)) (f' := (G : X × I → Y))
      hs₁ hps (ϕ := fun q v ↦ Φ q v) hΦ₁,
    Bundle.Pullback.continuous_totalSpaceMap_comp_right
      (E₁ := E) (E₂ := E) (f' := (G : X × I → Y)) (f := (G : X × I → Y))
      hs₁ hps (ϕ := fun q v ↦ (Φ q).symm v) hΦ₂,
    fun x hx v ↦ ?_⟩
  dsimp only
  rw [hΦs ⟨x, hx⟩ 1]
  exact totalSpace_mk_eq_of_eq (hGs' ⟨x, hx⟩ 1) v

/-- **Relative homotopy invariance of vector bundles.** Over a paracompact R₁ space `X`, let
`s ⊆ X` be closed and let `f₀ f₁ : C(X, Y)` be homotopic relative to `s`. If `F` is a Banach space
whose endomorphism space `F →L[𝕜] F` has the Tietze extension property (for instance any
finite-dimensional space over `ℝ` or `ℂ`), there are fibrewise continuous linear equivalences
`Φ x : E (f₀ x) ≃L[𝕜] E (f₁ x)`, continuous on total spaces together with their inverses, that act
as the identity over every point of `s`. -/
theorem _root_.ContinuousMap.HomotopicRel.exists_continuousLinearEquiv_pullback {s : Set X}
    {f₀ f₁ : C(X, Y)} (h : f₀.HomotopicRel f₁ s) (hs : IsClosed s) :
    ∃ Φ : ∀ x, E (f₀ x) ≃L[𝕜] E (f₁ x),
      Continuous (fun v : TotalSpace F ((f₀ : X → Y) *ᵖ E) ↦
        TotalSpace.mk' F (E := (f₁ : X → Y) *ᵖ E) v.proj (Φ v.proj v.snd)) ∧
      Continuous (fun v : TotalSpace F ((f₁ : X → Y) *ᵖ E) ↦
        TotalSpace.mk' F (E := (f₀ : X → Y) *ᵖ E) v.proj ((Φ v.proj).symm v.snd)) ∧
      ∀ x ∈ s, ∀ v : E (f₀ x), (⟨f₁ x, Φ x v⟩ : TotalSpace F E) = ⟨f₀ x, v⟩ := by
  obtain ⟨H⟩ := h
  exact exists_continuousLinearEquiv_pullback_rel_of_eq (H.toContinuousMap.comp .prodSwap) hs
    H.apply_zero H.apply_one fun x hx t ↦ H.eq_fst t hx

end RelativeHomotopy

end TauCeti
