/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.Geometry.Manifold.FiberBundle.Principal.Classification
public import TauCeti.Topology.FiberBundle.Principal.Extension

/-!
# Smooth extension of the structure group of a principal bundle

For a `C^n` principal `G`-bundle `P` over `B` and a `C^n` group homomorphism `ρ : G →* H` into a
group `H` with `C^n` multiplication, `TauCeti.PrincipalBundle.Extend P ρ hρ` (`P ×_ρ H`) is a `C^n`
fibre bundle (`TauCeti.PrincipalBundle.Extend.contMDiffFiberBundle`). Because the source model `IG`
and the smoothness proof `ContMDiff IG IH n ρ` cannot be recovered by typeclass synthesis,
`Extend.contMDiffFiberBundle` is a theorem rather than a global instance: callers that need
`ContMDiffFiberBundle` or `IsManifold` on `ManifoldTotalSpace H (Extend P ρ hρ)` should install it
locally (e.g. `haveI := Extend.contMDiffFiberBundle IG hρ'`).

We prove `C^n` smoothness of `(p, h) ↦ [p, h]` and `p ↦ [p, 1]` in fibre charts, smooth universal
comparison (`diffeomorphOfEquivariant`), congruence (`congrDiffeomorph`), functoriality under
identity and composition (`idDiffeomorph`, `compDiffeomorph`), pullback (`pullbackDiffeomorph`),
associated-bundle identification (`associatedDiffeomorph`), and compatibility with pushforward on
nonabelian Čech `H¹` (`TauCeti.NonabelianCechH1.mk_coordChange_extend`).

## References

* S. Kobayashi, K. Nomizu, *Foundations of Differential Geometry I*, Interscience, 1963, Ch. I, §5.
* I. Kolář, P. W. Michor, J. Slovák, *Natural Operations in Differential Geometry*, Springer,
  1993, §§10.5–10.7.
-/

public section

noncomputable section

open Bundle Filter MulOpposite Set TauCeti TauCeti.ManifoldTotalSpace TauCeti.PrincipalBundle
open scoped Manifold ContDiff Topology

section SmoothBase
variable {n : ℕ∞ω} {𝕜 B G : Type*} [NontriviallyNormedField 𝕜]
  {EB HB : Type*} [NormedAddCommGroup EB] [NormedSpace 𝕜 EB] [TopologicalSpace HB]
  {IB : ModelWithCorners 𝕜 EB HB} [TopologicalSpace B] [ChartedSpace HB B]
  [Group G] [TopologicalSpace G]
  {P : B → Type*} [TopologicalSpace (TotalSpace G P)] [∀ b, TopologicalSpace (P b)]
  [FiberBundle G P] [∀ b, MulAction Gᵐᵒᵖ (P b)] [PrincipalBundle G P]

section SmoothExtend
variable {H M EG HG EH HH EM HM : Type*}
  [NormedAddCommGroup EG] [NormedSpace 𝕜 EG] [TopologicalSpace HG] {IG : ModelWithCorners 𝕜 EG HG}
  [ChartedSpace HG G] [NormedAddCommGroup EH] [NormedSpace 𝕜 EH] [TopologicalSpace HH]
  {IH : ModelWithCorners 𝕜 EH HH} [Group H] [TopologicalSpace H] [ChartedSpace HH H]
  [ContinuousMul H] [ContMDiffMul IH n H]
  [NormedAddCommGroup EM] [NormedSpace 𝕜 EM] [TopologicalSpace HM] {IM : ModelWithCorners 𝕜 EM HM}
  [TopologicalSpace M] [ChartedSpace HM M]

variable (IG) in
/-- **Smooth structure-group extension.** When `P` is a `C^n` principal `G`-bundle, `H` has `C^n`
multiplication, and `ρ : G →* H` is `C^n`, `Extend P ρ hρ` is a `C^n` fibre bundle.

This is a theorem rather than a global instance because `IG` and `ContMDiff IG IH n ρ` cannot be
synthesized from the target type; install it locally with `haveI := Extend.contMDiffFiberBundle ...`
when `ContMDiffFiberBundle` or `IsManifold` is needed. -/
theorem TauCeti.PrincipalBundle.Extend.contMDiffFiberBundle [hP : ContMDiffFiberBundle n G P IB IG]
    {ρ : G →* H} {hρ : Continuous ρ} (hρ' : ContMDiff IG IH n ρ) :
    ContMDiffFiberBundle n H (Extend P ρ hρ) IB IH := by
  refine (TauCeti.PrincipalBundle.contMDiffFiberBundle_iff n H IB IH (Extend P ρ hρ)).2
    fun e e' he he' ↦ ?_
  obtain ⟨b, rfl⟩ := he.out; obtain ⟨b', rfl⟩ := he'.out
  rw [← Extend.trivializationAt_eq_localTriv ρ hρ b,
    ← Extend.trivializationAt_eq_localTriv ρ hρ b',
    Extend.baseSet_trivializationAt, Extend.baseSet_trivializationAt]
  have htr : ContMDiffOn IB IG n
      (fun x ↦ (trivializationAt G P b).coordChange (trivializationAt G P b') x 1)
      ((trivializationAt G P b).baseSet ∩ (trivializationAt G P b').baseSet) :=
    (hP.contMDiffOn_coordChange (trivializationAt G P b) (trivializationAt G P b')).comp
      (contMDiffOn_id.prodMk contMDiffOn_const) fun _ hx ↦ ⟨hx, mem_univ _⟩
  refine (hρ'.comp_contMDiffOn htr).congr fun x hx ↦ ?_
  rw [Function.comp_apply, Extend.coordChange_trivializationAt ρ hρ hx.1 hx.2 1, mul_one]

section
variable {ρ : G →* H} {f : M → B} {p : ∀ x, P (f x)} {h : M → H} {s : Set M} {x₀ : M}

/-- `C^n` regularity within a set at a point of `x ↦ ⟨f x, Extend.mk ρ hρ (p x) (h x)⟩`. -/
theorem ContMDiffWithinAt.totalSpaceMk_extendMk (hρ : Continuous ρ)
    (hp : ContMDiffWithinAt IM (IB.prod IG) n (fun x ↦ homeomorph G P ⟨f x, p x⟩) s x₀)
    (hh : ContMDiffWithinAt IM IH n h s x₀) (hρ' : ContMDiff IG IH n ρ) :
    ContMDiffWithinAt IM (IB.prod IH) n
      (fun x ↦ homeomorph H (Extend P ρ hρ) ⟨f x, Extend.mk ρ hρ (p x) (h x)⟩) s x₀ := by
  rw [ManifoldTotalSpace.contMDiffWithinAt_iff] at hp ⊢
  obtain ⟨hf, hp⟩ := hp; have hx₀ := mem_baseSet_trivializationAt G P (f x₀)
  refine ⟨hf, ((hρ'.contMDiffAt.comp_contMDiffWithinAt x₀ hp).mul hh).congr_of_eventuallyEq ?_
    (Extend.trivializationAt_mk_snd ρ hρ hx₀ _ _)⟩
  filter_upwards [hf.continuousWithinAt
    ((trivializationAt G P (f x₀)).open_baseSet.mem_nhds hx₀)] with x hx
  exact Extend.trivializationAt_mk_snd ρ hρ hx _ _

/-- `C^n` regularity at a point of `x ↦ ⟨f x, Extend.mk ρ hρ (p x) (h x)⟩`. -/
theorem ContMDiffAt.totalSpaceMk_extendMk (hρ : Continuous ρ)
    (hp : ContMDiffAt IM (IB.prod IG) n (fun x ↦ homeomorph G P ⟨f x, p x⟩) x₀)
    (hh : ContMDiffAt IM IH n h x₀) (hρ' : ContMDiff IG IH n ρ) :
    ContMDiffAt IM (IB.prod IH) n
      (fun x ↦ homeomorph H (Extend P ρ hρ) ⟨f x, Extend.mk ρ hρ (p x) (h x)⟩) x₀ :=
  ContMDiffWithinAt.totalSpaceMk_extendMk hρ hp hh hρ'

/-- `C^n` regularity on a set of `x ↦ ⟨f x, Extend.mk ρ hρ (p x) (h x)⟩`. -/
theorem ContMDiffOn.totalSpaceMk_extendMk (hρ : Continuous ρ)
    (hp : ContMDiffOn IM (IB.prod IG) n (fun x ↦ homeomorph G P ⟨f x, p x⟩) s)
    (hh : ContMDiffOn IM IH n h s) (hρ' : ContMDiff IG IH n ρ) :
    ContMDiffOn IM (IB.prod IH) n
      (fun x ↦ homeomorph H (Extend P ρ hρ) ⟨f x, Extend.mk ρ hρ (p x) (h x)⟩) s :=
  fun x hx ↦ (hp x hx).totalSpaceMk_extendMk hρ (hh x hx) hρ'

/-- Global `C^n` regularity of `x ↦ ⟨f x, Extend.mk ρ hρ (p x) (h x)⟩`. -/
theorem ContMDiff.totalSpaceMk_extendMk (hρ : Continuous ρ)
    (hp : ContMDiff IM (IB.prod IG) n fun x ↦ homeomorph G P ⟨f x, p x⟩)
    (hh : ContMDiff IM IH n h) (hρ' : ContMDiff IG IH n ρ) :
    ContMDiff IM (IB.prod IH) n
      fun x ↦ homeomorph H (Extend P ρ hρ) ⟨f x, Extend.mk ρ hρ (p x) (h x)⟩ :=
  fun x ↦ (hp x).totalSpaceMk_extendMk hρ (hh x) hρ'
end

namespace TauCeti.PrincipalBundle.Extend
/-- The quotient map `ManifoldTotalSpace G P × H → ManifoldTotalSpace H (Extend P ρ hρ)` is
`C^n`. -/
theorem contMDiff_totalSpaceMk_mk {ρ : G →* H} (hρ : Continuous ρ) (hρ' : ContMDiff IG IH n ρ) :
    ContMDiff ((IB.prod IG).prod IH) (IB.prod IH) n
      (fun x : ManifoldTotalSpace G P × H ↦ homeomorph H (Extend P ρ hρ)
        ⟨((homeomorph G P).symm x.1).proj, mk ρ hρ ((homeomorph G P).symm x.1).snd x.2⟩) :=
  (contMDiff_fst.congr fun x : ManifoldTotalSpace G P × H ↦ by
    simp only [TotalSpace.eta, Homeomorph.apply_symm_apply]).totalSpaceMk_extendMk
    hρ contMDiff_snd hρ'

/-- The canonical `ρ`-equivariant map `inl : ManifoldTotalSpace G P → ManifoldTotalSpace H
(Extend P ρ hρ)` is `C^n`. -/
theorem contMDiff_inl {ρ : G →* H} (hρ : Continuous ρ) (hρ' : ContMDiff IG IH n ρ) :
    ContMDiff (IB.prod IG) (IB.prod IH) n
      (fun x : ManifoldTotalSpace G P ↦ homeomorph H (Extend P ρ hρ)
        ⟨((homeomorph G P).symm x).proj, inl ρ hρ ((homeomorph G P).symm x).snd⟩) := by
  simpa only [inl_def] using
    (contMDiff_id.congr fun x : ManifoldTotalSpace G P ↦ by
      simp only [TotalSpace.eta, Homeomorph.apply_symm_apply, id_eq]).totalSpaceMk_extendMk
      hρ contMDiff_const hρ'
end TauCeti.PrincipalBundle.Extend
end SmoothExtend

namespace TauCeti.PrincipalBundle.Extend

section ReductionDiffeomorph
variable {H EG HG EH HH : Type*}
  [NormedAddCommGroup EG] [NormedSpace 𝕜 EG] [TopologicalSpace HG] {IG : ModelWithCorners 𝕜 EG HG}
  [ChartedSpace HG G] [NormedAddCommGroup EH] [NormedSpace 𝕜 EH] [TopologicalSpace HH]
  {IH : ModelWithCorners 𝕜 EH HH} [Group H] [TopologicalSpace H] [ChartedSpace HH H]
  [ContinuousMul H] [LieGroup IH n H]
  {Q : B → Type*} [TopologicalSpace (TotalSpace H Q)] [∀ b, TopologicalSpace (Q b)]
  [FiberBundle H Q] [∀ b, MulAction Hᵐᵒᵖ (Q b)] [PrincipalBundle H Q]
  (ρ : G →* H) (hρ : Continuous ρ) (φ : ∀ b, P b → Q b)
  (hφ : ∀ b (p : P b) (g : G), φ b (op g • p) = op (ρ g) • φ b p)
  (hφc : ContMDiff (IB.prod IG) (IB.prod IH) n (fun x : ManifoldTotalSpace G P ↦ homeomorph H Q
    ⟨((homeomorph G P).symm x).proj, φ _ ((homeomorph G P).symm x).snd⟩))

/-- **Smooth universal comparison.** When `H` is a `C^n` Lie group, any `C^n` `ρ`-equivariant map
`φ : P → Q` extends to an `H`-equivariant `C^n` diffeomorphism `Extend P ρ hρ ≃ₘ^n Q` over `B`. -/
def diffeomorphOfEquivariant :
    ManifoldTotalSpace H (Extend P ρ hρ) ≃ₘ^n⟮IB.prod IH, IB.prod IH⟯ ManifoldTotalSpace H Q :=
  PrincipalBundle.diffeomorphOfEquivariant H (fun b ↦ equivOfEquivariant ρ hρ φ hφ b)
    (equivOfEquivariant_smul ρ hρ φ hφ) <| by
    have (b : B) : Nonempty (P b) := ⟨(FiberBundle.homeomorphAt G P b).symm 1⟩
    intro x₀
    let b₀ := ((homeomorph H (Extend P ρ hρ)).symm x₀).proj
    let eP := trivializationAt G P b₀
    have hπ := contMDiff_proj n H (Extend P ρ hρ) IB IH x₀
    refine ((contMDiffAt_section_comp 1 hφc.contMDiffAt hπ).totalSpaceMk_smul
      (contMDiffAt_trivializationAt_snd n IB IH x₀)).congr_of_eventuallyEq ?_
    filter_upwards [hπ.continuousAt.preimage_mem_nhds
      (eP.open_baseSet.mem_nhds (mem_baseSet_trivializationAt G P b₀))] with y hy
    obtain ⟨⟨b, z⟩, rfl⟩ := (homeomorph H (Extend P ρ hρ)).surjective y
    have hbP : b ∈ eP.baseSet := by simpa using hy
    obtain ⟨h, rfl⟩ := (mk_bijective ρ hρ (eP.symm b 1)).surjective z
    rw [fiberwiseMap_homeomorph]
    dsimp only [Function.comp_def]; rw [Homeomorph.symm_apply_apply]
    exact congrArg (fun w ↦ homeomorph H Q ⟨b, w⟩) <| by
      rw [equivOfEquivariant_mk, trivializationAt_mk_snd ρ hρ hbP,
        congrArg Prod.snd (eP.apply_mk_symm hbP 1), map_one, one_mul]

@[simp] theorem diffeomorphOfEquivariant_apply (z : TotalSpace H (Extend P ρ hρ)) :
    diffeomorphOfEquivariant ρ hρ φ hφ hφc (homeomorph H _ z) =
      homeomorph H Q ⟨z.proj, equivOfEquivariant ρ hρ φ hφ z.proj z.snd⟩ :=
  PrincipalBundle.diffeomorphOfEquivariant_apply _ _ _ z
@[simp] theorem diffeomorphOfEquivariant_symm_apply (q : TotalSpace H Q) :
    (diffeomorphOfEquivariant ρ hρ φ hφ hφc).symm (homeomorph H Q q) =
      homeomorph H _ ⟨q.proj, (equivOfEquivariant ρ hρ φ hφ q.proj).symm q.snd⟩ :=
  PrincipalBundle.diffeomorphOfEquivariant_symm_apply _ _ _ q
@[simp] theorem homeomorph_symm_diffeomorphOfEquivariant_apply
    (x : ManifoldTotalSpace H (Extend P ρ hρ)) :
    (homeomorph H Q).symm (diffeomorphOfEquivariant ρ hρ φ hφ hφc x) =
      ⟨((homeomorph H _).symm x).proj,
        equivOfEquivariant ρ hρ φ hφ _ ((homeomorph H _).symm x).snd⟩ :=
  PrincipalBundle.homeomorph_symm_diffeomorphOfEquivariant_apply _ _ _ x
@[simp] theorem homeomorph_symm_diffeomorphOfEquivariant_symm_apply (x : ManifoldTotalSpace H Q) :
    (homeomorph H _).symm ((diffeomorphOfEquivariant ρ hρ φ hφ hφc).symm x) =
      ⟨((homeomorph H Q).symm x).proj,
        (equivOfEquivariant ρ hρ φ hφ _).symm ((homeomorph H Q).symm x).snd⟩ :=
  PrincipalBundle.homeomorph_symm_diffeomorphOfEquivariant_symm_apply _ _ _ x
theorem diffeomorphOfEquivariant_mk {b : B} (p : P b) (h : H) :
    diffeomorphOfEquivariant ρ hρ φ hφ hφc (homeomorph H _ ⟨b, mk ρ hρ p h⟩) =
      homeomorph H Q ⟨b, op h • φ b p⟩ := by
  rw [diffeomorphOfEquivariant_apply, equivOfEquivariant_mk]
theorem diffeomorphOfEquivariant_inl {b : B} (p : P b) :
    diffeomorphOfEquivariant ρ hρ φ hφ hφc (homeomorph H _ ⟨b, inl ρ hρ p⟩) =
      homeomorph H Q ⟨b, φ b p⟩ := by rw [diffeomorphOfEquivariant_apply, equivOfEquivariant_inl]
theorem diffeomorphOfEquivariant_symm_inl {b : B} (p : P b) :
    (diffeomorphOfEquivariant ρ hρ φ hφ hφc).symm (homeomorph H Q ⟨b, φ b p⟩) =
      homeomorph H _ ⟨b, inl ρ hρ p⟩ := by
  rw [diffeomorphOfEquivariant_symm_apply, equivOfEquivariant_symm_inl]
@[simp] theorem diffeomorphOfEquivariant_op_smul (h' : H)
    (x : ManifoldTotalSpace H (Extend P ρ hρ)) :
    diffeomorphOfEquivariant ρ hρ φ hφ hφc (op h' • x) =
      op h' • diffeomorphOfEquivariant ρ hρ φ hφ hφc x :=
  PrincipalBundle.diffeomorphOfEquivariant_op_smul _ _ _ h' x
@[simp] theorem diffeomorphOfEquivariant_symm_op_smul (h' : H) (x : ManifoldTotalSpace H Q) :
    (diffeomorphOfEquivariant ρ hρ φ hφ hφc).symm (op h' • x) =
      op h' • (diffeomorphOfEquivariant ρ hρ φ hφ hφc).symm x := by
  obtain ⟨q, rfl⟩ := (homeomorph H Q).surjective x; simp
end ReductionDiffeomorph

section Congr
variable {H EH HH : Type*} [NormedAddCommGroup EH] [NormedSpace 𝕜 EH] [TopologicalSpace HH]
  {IH : ModelWithCorners 𝕜 EH HH} [Group H] [TopologicalSpace H] [ContinuousMul H]
  [ChartedSpace HH H] {ρ₁ ρ₂ : G →* H} (h : ρ₁ = ρ₂) (hρ₁ : Continuous ρ₁) (hρ₂ : Continuous ρ₂)
/-- Equal homomorphisms produce canonically `C^n`-diffeomorphic extended total spaces. -/
def congrDiffeomorph :
    ManifoldTotalSpace H (Extend P ρ₁ hρ₁) ≃ₘ^n⟮IB.prod IH, IB.prod IH⟯
      ManifoldTotalSpace H (Extend P ρ₂ hρ₂) :=
  diffeomorphOfCoordEq (fun b ↦ congrEquiv h hρ₁ hρ₂ b) fun _ ↦
    Eventually.of_forall fun _ z ↦ trivializationAt_congrEquiv_snd h hρ₁ hρ₂ _ _ z
@[simp] theorem congrDiffeomorph_apply (z : TotalSpace H (Extend P ρ₁ hρ₁)) :
    congrDiffeomorph (n := n) (IB := IB) (IH := IH) h hρ₁ hρ₂ (homeomorph H _ z) =
      homeomorph H _ (congrHomeomorph h hρ₁ hρ₂ z) := by
  rw [congrHomeomorph_apply]; exact diffeomorphOfCoordEq_apply _ _ z
@[simp] theorem congrDiffeomorph_symm_apply (z : TotalSpace H (Extend P ρ₂ hρ₂)) :
    (congrDiffeomorph (n := n) (IB := IB) (IH := IH) h hρ₁ hρ₂).symm (homeomorph H _ z) =
      homeomorph H _ ((congrHomeomorph h hρ₁ hρ₂).symm z) := by
  rw [congrHomeomorph_symm_apply]; exact diffeomorphOfCoordEq_symm_apply _ _ z
@[simp] theorem homeomorph_symm_congrDiffeomorph_apply
    (x : ManifoldTotalSpace H (Extend P ρ₁ hρ₁)) :
    (homeomorph H _).symm (congrDiffeomorph (n := n) (IB := IB) (IH := IH) h hρ₁ hρ₂ x) =
      congrHomeomorph h hρ₁ hρ₂ ((homeomorph H _).symm x) := by
  rw [congrHomeomorph_apply]; exact homeomorph_symm_diffeomorphOfCoordEq_apply _ _ x
@[simp] theorem homeomorph_symm_congrDiffeomorph_symm_apply
    (x : ManifoldTotalSpace H (Extend P ρ₂ hρ₂)) :
    (homeomorph H _).symm ((congrDiffeomorph (n := n) (IB := IB) (IH := IH) h hρ₁ hρ₂).symm x) =
      (congrHomeomorph h hρ₁ hρ₂).symm ((homeomorph H _).symm x) := by
  rw [congrHomeomorph_symm_apply]; exact homeomorph_symm_diffeomorphOfCoordEq_symm_apply _ _ x
theorem congrDiffeomorph_mk {b : B} (p : P b) (x : H) :
    congrDiffeomorph (n := n) (IB := IB) (IH := IH) h hρ₁ hρ₂ (homeomorph H _ ⟨b, mk ρ₁ hρ₁ p x⟩) =
      homeomorph H _ ⟨b, mk ρ₂ hρ₂ p x⟩ := by rw [congrDiffeomorph_apply, congrHomeomorph_mk]
theorem congrDiffeomorph_symm_mk {b : B} (p : P b) (x : H) :
    (congrDiffeomorph (n := n) (IB := IB) (IH := IH) h hρ₁ hρ₂).symm
        (homeomorph H _ ⟨b, mk ρ₂ hρ₂ p x⟩) =
      homeomorph H _ ⟨b, mk ρ₁ hρ₁ p x⟩ := by
  rw [congrDiffeomorph_symm_apply, congrHomeomorph_symm_mk]
@[simp] theorem congrDiffeomorph_op_smul (a : H) (x : ManifoldTotalSpace H (Extend P ρ₁ hρ₁)) :
    congrDiffeomorph (n := n) (IB := IB) (IH := IH) h hρ₁ hρ₂ (op a • x) =
      op a • congrDiffeomorph (n := n) (IB := IB) (IH := IH) h hρ₁ hρ₂ x := by
  obtain ⟨z, rfl⟩ := (homeomorph H _).surjective x; simp [congrHomeomorph_apply]
@[simp] theorem congrDiffeomorph_symm_op_smul (a : H) (x : ManifoldTotalSpace H (Extend P ρ₂ hρ₂)) :
    (congrDiffeomorph (n := n) (IB := IB) (IH := IH) h hρ₁ hρ₂).symm (op a • x) =
      op a • (congrDiffeomorph (n := n) (IB := IB) (IH := IH) h hρ₁ hρ₂).symm x := by
  obtain ⟨z, rfl⟩ := (homeomorph H _).surjective x; simp [congrHomeomorph_symm_apply]
end Congr

section Id
variable {EG HG : Type*} [NormedAddCommGroup EG] [NormedSpace 𝕜 EG] [TopologicalSpace HG]
  {IG : ModelWithCorners 𝕜 EG HG} [ContinuousMul G] [ChartedSpace HG G]
/-- **Smooth identity extension.** `Extend P (MonoidHom.id G) continuous_id` is canonically `C^n`
diffeomorphic to `P` over `B` in the charts through the fibre. -/
def idDiffeomorph :
    ManifoldTotalSpace G (Extend P (MonoidHom.id G) continuous_id)
      ≃ₘ^n⟮IB.prod IG, IB.prod IG⟯ ManifoldTotalSpace G P :=
  diffeomorphOfCoordEq idEquiv fun b₀ ↦ mem_of_superset
    ((trivializationAt G P b₀).open_baseSet.mem_nhds (mem_baseSet_trivializationAt G P b₀))
    fun _ hb z ↦ trivializationAt_idEquiv_snd hb z
@[simp] theorem idDiffeomorph_apply (z : TotalSpace G (Extend P (MonoidHom.id G) continuous_id)) :
    idDiffeomorph (n := n) (IB := IB) (IG := IG) (homeomorph G _ z) =
      homeomorph G P (idHomeomorph z) := by
  rw [idHomeomorph_apply]; exact diffeomorphOfCoordEq_apply _ _ z
@[simp] theorem idDiffeomorph_symm_apply (z : TotalSpace G P) :
    (idDiffeomorph (n := n) (IB := IB) (IG := IG)).symm (homeomorph G P z) =
      homeomorph G _ ((idHomeomorph (G := G) (P := P)).symm z) := by
  rw [idHomeomorph_symm_apply, ← idEquiv_symm_apply]; exact diffeomorphOfCoordEq_symm_apply _ _ z
@[simp] theorem homeomorph_symm_idDiffeomorph_apply
    (x : ManifoldTotalSpace G (Extend P (MonoidHom.id G) continuous_id)) :
    (homeomorph G P).symm (idDiffeomorph (n := n) (IB := IB) (IG := IG) x) =
      idHomeomorph ((homeomorph G _).symm x) := by
  rw [idHomeomorph_apply]; exact homeomorph_symm_diffeomorphOfCoordEq_apply _ _ x
@[simp] theorem homeomorph_symm_idDiffeomorph_symm_apply (x : ManifoldTotalSpace G P) :
    (homeomorph G _).symm ((idDiffeomorph (n := n) (IB := IB) (IG := IG)).symm x) =
      (idHomeomorph (G := G) (P := P)).symm ((homeomorph G P).symm x) := by
  rw [idHomeomorph_symm_apply, ← idEquiv_symm_apply]
  exact homeomorph_symm_diffeomorphOfCoordEq_symm_apply _ _ x
theorem idDiffeomorph_mk {b : B} (p : P b) (g : G) :
    idDiffeomorph (n := n) (IB := IB) (IG := IG)
        (homeomorph G _ ⟨b, mk (MonoidHom.id G) continuous_id p g⟩) =
      homeomorph G P ⟨b, op g • p⟩ := by rw [idDiffeomorph_apply, idHomeomorph_mk]
@[simp] theorem idDiffeomorph_op_smul (g : G)
    (x : ManifoldTotalSpace G (Extend P (MonoidHom.id G) continuous_id)) :
    idDiffeomorph (n := n) (IB := IB) (IG := IG) (op g • x) =
      op g • idDiffeomorph (n := n) (IB := IB) (IG := IG) x := by
  obtain ⟨z, rfl⟩ := (homeomorph G _).surjective x; simp [idHomeomorph_apply]
@[simp] theorem idDiffeomorph_symm_op_smul (g : G) (x : ManifoldTotalSpace G P) :
    (idDiffeomorph (n := n) (IB := IB) (IG := IG)).symm (op g • x) =
      op g • (idDiffeomorph (n := n) (IB := IB) (IG := IG)).symm x := by
  obtain ⟨z, rfl⟩ := (homeomorph G P).surjective x; simp [idHomeomorph_symm_apply]
end Id

section Comp
variable {H K EK HK : Type*} [Group H] [TopologicalSpace H] [ContinuousMul H]
  [NormedAddCommGroup EK] [NormedSpace 𝕜 EK] [TopologicalSpace HK] {IK : ModelWithCorners 𝕜 EK HK}
  [Group K] [TopologicalSpace K] [ContinuousMul K] [ChartedSpace HK K]
  (ρ : G →* H) (hρ : Continuous ρ) (σ : H →* K) (hσ : Continuous σ)
/-- **Smooth functoriality of structure-group extension under composition.** -/
def compDiffeomorph :
    ManifoldTotalSpace K (Extend (Extend P ρ hρ) σ hσ) ≃ₘ^n⟮IB.prod IK, IB.prod IK⟯
      ManifoldTotalSpace K (Extend P (σ.comp ρ) (hσ.comp hρ)) :=
  diffeomorphOfCoordEq (compEquiv ρ hρ σ hσ) fun b₀ ↦ mem_of_superset
    ((trivializationAt G P b₀).open_baseSet.mem_nhds (mem_baseSet_trivializationAt G P b₀))
    fun _ hb z ↦ trivializationAt_compEquiv_snd ρ hρ σ hσ hb z
@[simp] theorem compDiffeomorph_apply (z : TotalSpace K (Extend (Extend P ρ hρ) σ hσ)) :
    compDiffeomorph (n := n) (IB := IB) (IK := IK) ρ hρ σ hσ (homeomorph K _ z) =
      homeomorph K _ (compHomeomorph ρ hρ σ hσ z) := by
  rw [compHomeomorph_apply]; exact diffeomorphOfCoordEq_apply _ _ z
@[simp] theorem compDiffeomorph_symm_apply (z : TotalSpace K (Extend P (σ.comp ρ) (hσ.comp hρ))) :
    (compDiffeomorph (n := n) (IB := IB) (IK := IK) ρ hρ σ hσ).symm (homeomorph K _ z) =
      homeomorph K _ ((compHomeomorph ρ hρ σ hσ).symm z) := by
  rw [compHomeomorph_symm_apply]; exact diffeomorphOfCoordEq_symm_apply _ _ z
@[simp] theorem homeomorph_symm_compDiffeomorph_apply
    (x : ManifoldTotalSpace K (Extend (Extend P ρ hρ) σ hσ)) :
    (homeomorph K _).symm (compDiffeomorph (n := n) (IB := IB) (IK := IK) ρ hρ σ hσ x) =
      compHomeomorph ρ hρ σ hσ ((homeomorph K _).symm x) := by
  rw [compHomeomorph_apply]; exact homeomorph_symm_diffeomorphOfCoordEq_apply _ _ x
@[simp] theorem homeomorph_symm_compDiffeomorph_symm_apply
    (x : ManifoldTotalSpace K (Extend P (σ.comp ρ) (hσ.comp hρ))) :
    (homeomorph K _).symm ((compDiffeomorph (n := n) (IB := IB) (IK := IK) ρ hρ σ hσ).symm x) =
      (compHomeomorph ρ hρ σ hσ).symm ((homeomorph K _).symm x) := by
  rw [compHomeomorph_symm_apply]; exact homeomorph_symm_diffeomorphOfCoordEq_symm_apply _ _ x
theorem compDiffeomorph_mk {b : B} (p : P b) (h : H) (k : K) :
    compDiffeomorph (n := n) (IB := IB) (IK := IK) ρ hρ σ hσ
        (homeomorph K _ ⟨b, mk σ hσ (mk ρ hρ p h) k⟩) =
      homeomorph K _ ⟨b, mk (σ.comp ρ) (hσ.comp hρ) p (σ h * k)⟩ := by
  rw [compDiffeomorph_apply, compHomeomorph_mk]
theorem compDiffeomorph_symm_mk {b : B} (p : P b) (k : K) :
    (compDiffeomorph (n := n) (IB := IB) (IK := IK) ρ hρ σ hσ).symm
        (homeomorph K _ ⟨b, mk (σ.comp ρ) (hσ.comp hρ) p k⟩) =
      homeomorph K _ ⟨b, mk σ hσ (inl ρ hρ p) k⟩ := by
  rw [compDiffeomorph_symm_apply, compHomeomorph_symm_mk]
@[simp] theorem compDiffeomorph_op_smul (k : K)
    (x : ManifoldTotalSpace K (Extend (Extend P ρ hρ) σ hσ)) :
    compDiffeomorph (n := n) (IB := IB) (IK := IK) ρ hρ σ hσ (op k • x) =
      op k • compDiffeomorph (n := n) (IB := IB) (IK := IK) ρ hρ σ hσ x := by
  obtain ⟨z, rfl⟩ := (homeomorph K _).surjective x; simp [compHomeomorph_apply]
@[simp] theorem compDiffeomorph_symm_op_smul (k : K)
    (x : ManifoldTotalSpace K (Extend P (σ.comp ρ) (hσ.comp hρ))) :
    (compDiffeomorph (n := n) (IB := IB) (IK := IK) ρ hρ σ hσ).symm (op k • x) =
      op k • (compDiffeomorph (n := n) (IB := IB) (IK := IK) ρ hρ σ hσ).symm x := by
  obtain ⟨z, rfl⟩ := (homeomorph K _).surjective x; simp [compHomeomorph_symm_apply]
end Comp

section Associated
variable {H F EF HF : Type*} [Group H] [TopologicalSpace H] [ContinuousMul H]
  [NormedAddCommGroup EF] [NormedSpace 𝕜 EF] [TopologicalSpace HF] {IF : ModelWithCorners 𝕜 EF HF}
  [TopologicalSpace F] [ChartedSpace HF F]
  [MulAction H F] [ContinuousSMul H F] [MulAction G F] [ContinuousSMul G F]
  (ρ : G →* H) (hρ : Continuous ρ) (hF : ∀ (g : G) (v : F), g • v = ρ g • v)
/-- **Smooth associated bundle of an extended principal bundle.** `(P ×_ρ H) ×_H F ≃ₘ^n P ×_G F`
when `G` acts on `F` through `ρ`. -/
def associatedDiffeomorph :
    ManifoldTotalSpace F (AssociatedBundle H (Extend P ρ hρ) F) ≃ₘ^n⟮IB.prod IF, IB.prod IF⟯
      ManifoldTotalSpace F (AssociatedBundle G P F) :=
  diffeomorphOfCoordEq (associatedEquiv ρ hρ hF) fun b₀ ↦ mem_of_superset
    ((trivializationAt G P b₀).open_baseSet.mem_nhds (mem_baseSet_trivializationAt G P b₀))
    fun _ hb z ↦ trivializationAt_associatedEquiv_snd ρ hρ hF hb z
@[simp] theorem associatedDiffeomorph_apply
    (z : TotalSpace F (AssociatedBundle H (Extend P ρ hρ) F)) :
    associatedDiffeomorph (n := n) (IB := IB) (IF := IF) ρ hρ hF (homeomorph F _ z) =
      homeomorph F _ (associatedHomeomorph ρ hρ hF z) := by
  rw [associatedHomeomorph_apply]; exact diffeomorphOfCoordEq_apply _ _ z
@[simp] theorem associatedDiffeomorph_symm_apply (z : TotalSpace F (AssociatedBundle G P F)) :
    (associatedDiffeomorph (n := n) (IB := IB) (IF := IF) ρ hρ hF).symm (homeomorph F _ z) =
      homeomorph F _ ((associatedHomeomorph ρ hρ hF).symm z) := by
  rw [associatedHomeomorph_symm_apply]; exact diffeomorphOfCoordEq_symm_apply _ _ z
@[simp] theorem homeomorph_symm_associatedDiffeomorph_apply
    (x : ManifoldTotalSpace F (AssociatedBundle H (Extend P ρ hρ) F)) :
    (homeomorph F _).symm (associatedDiffeomorph (n := n) (IB := IB) (IF := IF) ρ hρ hF x) =
      associatedHomeomorph ρ hρ hF ((homeomorph F _).symm x) := by
  rw [associatedHomeomorph_apply]; exact homeomorph_symm_diffeomorphOfCoordEq_apply _ _ x
@[simp] theorem homeomorph_symm_associatedDiffeomorph_symm_apply
    (x : ManifoldTotalSpace F (AssociatedBundle G P F)) :
    (homeomorph F _).symm ((associatedDiffeomorph (n := n) (IB := IB) (IF := IF) ρ hρ hF).symm x) =
      (associatedHomeomorph ρ hρ hF).symm ((homeomorph F _).symm x) := by
  rw [associatedHomeomorph_symm_apply]; exact homeomorph_symm_diffeomorphOfCoordEq_symm_apply _ _ x
theorem associatedDiffeomorph_mk {b : B} (p : P b) (h : H) (v : F) :
    associatedDiffeomorph (n := n) (IB := IB) (IF := IF) ρ hρ hF
        (homeomorph F _ ⟨b, AssociatedBundle.mk H (mk ρ hρ p h) v⟩) =
      homeomorph F _ ⟨b, AssociatedBundle.mk G p (h • v)⟩ := by
  rw [associatedDiffeomorph_apply, associatedHomeomorph_mk]
theorem associatedDiffeomorph_symm_mk {b : B} (p : P b) (v : F) :
    (associatedDiffeomorph (n := n) (IB := IB) (IF := IF) ρ hρ hF).symm
        (homeomorph F _ ⟨b, AssociatedBundle.mk G p v⟩) =
      homeomorph F _ ⟨b, AssociatedBundle.mk H (inl ρ hρ p) v⟩ := by
  rw [associatedDiffeomorph_symm_apply, associatedHomeomorph_symm_mk]
end Associated

end TauCeti.PrincipalBundle.Extend

namespace TauCeti.NonabelianCechH1
variable {ι H EG HG EH HH : Type*}
  [NormedAddCommGroup EG] [NormedSpace 𝕜 EG] [TopologicalSpace HG] {IG : ModelWithCorners 𝕜 EG HG}
  [ChartedSpace HG G] [LieGroup IG n G] [ContMDiffFiberBundle n G P IB IG]
  [NormedAddCommGroup EH] [NormedSpace 𝕜 EH] [TopologicalSpace HH] {IH : ModelWithCorners 𝕜 EH HH}
  [Group H] [TopologicalSpace H] [ChartedSpace HH H] [ContinuousMul H] [LieGroup IH n H]

/-- The nonabelian Čech `H¹` transition-cocycle class of the extended principal bundle
`Extend P ρ hρ` is the pushforward along `ρ` of the transition-cocycle class of `P`. -/
theorem mk_coordChange_extend (u : ι → B) {U : ι → Set B}
    (hu : ∀ i, (trivializationAt G P (u i)).baseSet = U i)
    (ρ : G →* H) (hρ : Continuous ρ) (hρ' : ContMDiff IG IH n ρ) :
    mk (fun i j x ↦ (trivializationAt H (Extend P ρ hρ) (u i)).coordChange
          (trivializationAt H (Extend P ρ hρ) (u j)) x 1)
        (letI : ContMDiffFiberBundle n H (Extend P ρ hρ) IB IH :=
          Extend.contMDiffFiberBundle (P := P) (IB := IB) (hρ := hρ) IG hρ'
        isContMDiffGroupCocycle_coordChange IB IH n
          (fun i ↦ trivializationAt H (Extend P ρ hρ) (u i))
          (fun i ↦ (Extend.baseSet_trivializationAt ρ hρ (u i)).trans (hu i))) =
      map ρ hρ'
        (mk (fun i j x ↦ (trivializationAt G P (u i)).coordChange (trivializationAt G P (u j)) x 1)
          (isContMDiffGroupCocycle_coordChange IB IG n
            (fun i ↦ trivializationAt G P (u i)) hu)) := by
  rw [map_mk]
  refine mk_eq_mk_iff.2 (.of_eqOn fun i j x hx ↦ ?_)
  rw [Extend.coordChange_trivializationAt ρ hρ ((hu i).symm ▸ hx.1) ((hu j).symm ▸ hx.2) 1, mul_one]
end TauCeti.NonabelianCechH1
end SmoothBase

namespace TauCeti.PrincipalBundle.Extend
section Pullback
variable {n : ℕ∞ω} {𝕜 B B' G H EB' HB' EH HH : Type*} [NontriviallyNormedField 𝕜]
  [TopologicalSpace B] [NormedAddCommGroup EB'] [NormedSpace 𝕜 EB'] [TopologicalSpace HB']
  {IB' : ModelWithCorners 𝕜 EB' HB'} [TopologicalSpace B'] [ChartedSpace HB' B']
  [NormedAddCommGroup EH] [NormedSpace 𝕜 EH] [TopologicalSpace HH] {IH : ModelWithCorners 𝕜 EH HH}
  [Group H] [TopologicalSpace H] [ContinuousMul H] [ChartedSpace HH H] [Group G]
  [TopologicalSpace G] {P : B → Type*} [TopologicalSpace (TotalSpace G P)]
  [∀ b, TopologicalSpace (P b)] [FiberBundle G P] [∀ b, Nonempty (P b)] [∀ b, MulAction Gᵐᵒᵖ (P b)]
  [PrincipalBundle G P] {M : Type*} [FunLike M B' B] [ContinuousMapClass M B' B]
  (f : M) (ρ : G →* H) (hρ : Continuous ρ)

/-- **Smooth pullback comparison for structure-group extension.** -/
def pullbackDiffeomorph :
    ManifoldTotalSpace H (Extend ((f : B' → B) *ᵖ P) ρ hρ) ≃ₘ^n⟮IB'.prod IH, IB'.prod IH⟯
      ManifoldTotalSpace H ((f : B' → B) *ᵖ (Extend P ρ hρ)) :=
  diffeomorphOfCoordEq (pullbackEquiv f ρ hρ) fun x₀ ↦ mem_of_superset
    ((map_continuous f).continuousAt.preimage_mem_nhds
      ((trivializationAt G P (f x₀)).open_baseSet.mem_nhds
        (mem_baseSet_trivializationAt G P (f x₀)))) fun _ hx z ↦ by
      rw [Pullback.trivializationAt_snd]; dsimp only [Pullback.lift]
      exact trivializationAt_pullbackEquiv_snd f ρ hρ hx z
@[simp] theorem pullbackDiffeomorph_apply (z : TotalSpace H (Extend ((f : B' → B) *ᵖ P) ρ hρ)) :
    pullbackDiffeomorph (n := n) (IB' := IB') (IH := IH) f ρ hρ (homeomorph H _ z) =
      homeomorph H _ (pullbackHomeomorph f ρ hρ z) := by
  rw [pullbackHomeomorph_apply]; exact diffeomorphOfCoordEq_apply _ _ z
@[simp] theorem pullbackDiffeomorph_symm_apply
    (z : TotalSpace H ((f : B' → B) *ᵖ (Extend P ρ hρ))) :
    (pullbackDiffeomorph (n := n) (IB' := IB') (IH := IH) f ρ hρ).symm (homeomorph H _ z) =
      homeomorph H _ ((pullbackHomeomorph f ρ hρ).symm z) := by
  rw [pullbackHomeomorph_symm_apply]; exact diffeomorphOfCoordEq_symm_apply _ _ z
@[simp] theorem homeomorph_symm_pullbackDiffeomorph_apply
    (x : ManifoldTotalSpace H (Extend ((f : B' → B) *ᵖ P) ρ hρ)) :
    (homeomorph H _).symm (pullbackDiffeomorph (n := n) (IB' := IB') (IH := IH) f ρ hρ x) =
      pullbackHomeomorph f ρ hρ ((homeomorph H _).symm x) := by
  rw [pullbackHomeomorph_apply]; exact homeomorph_symm_diffeomorphOfCoordEq_apply _ _ x
@[simp] theorem homeomorph_symm_pullbackDiffeomorph_symm_apply
    (x : ManifoldTotalSpace H ((f : B' → B) *ᵖ (Extend P ρ hρ))) :
    (homeomorph H _).symm ((pullbackDiffeomorph (n := n) (IB' := IB') (IH := IH) f ρ hρ).symm x) =
      (pullbackHomeomorph f ρ hρ).symm ((homeomorph H _).symm x) := by
  rw [pullbackHomeomorph_symm_apply]; exact homeomorph_symm_diffeomorphOfCoordEq_symm_apply _ _ x
theorem pullbackDiffeomorph_mk (x : B') (p : P (f x)) (h : H) :
    pullbackDiffeomorph (n := n) (IB' := IB') (IH := IH) f ρ hρ
        (homeomorph H _ ⟨x, mk (P := (f : B' → B) *ᵖ P) ρ hρ p h⟩) =
      homeomorph H _ ⟨x, mk (P := P) ρ hρ p h⟩ := by
  rw [pullbackDiffeomorph_apply, pullbackHomeomorph_mk]
theorem pullbackDiffeomorph_symm_mk (x : B') (p : P (f x)) (h : H) :
    (pullbackDiffeomorph (n := n) (IB' := IB') (IH := IH) f ρ hρ).symm
        (homeomorph H _ ⟨x, mk (P := P) ρ hρ p h⟩) =
      homeomorph H _ ⟨x, mk (P := (f : B' → B) *ᵖ P) ρ hρ p h⟩ := by
  rw [pullbackDiffeomorph_symm_apply, pullbackHomeomorph_symm_mk]
@[simp] theorem pullbackDiffeomorph_op_smul (h' : H)
    (x : ManifoldTotalSpace H (Extend ((f : B' → B) *ᵖ P) ρ hρ)) :
    pullbackDiffeomorph (n := n) (IB' := IB') (IH := IH) f ρ hρ (op h' • x) =
      op h' • pullbackDiffeomorph (n := n) (IB' := IB') (IH := IH) f ρ hρ x := by
  obtain ⟨z, rfl⟩ := (homeomorph H _).surjective x; simp [pullbackHomeomorph_apply]
@[simp] theorem pullbackDiffeomorph_symm_op_smul (h' : H)
    (x : ManifoldTotalSpace H ((f : B' → B) *ᵖ (Extend P ρ hρ))) :
    (pullbackDiffeomorph (n := n) (IB' := IB') (IH := IH) f ρ hρ).symm (op h' • x) =
      op h' • (pullbackDiffeomorph (n := n) (IB' := IB') (IH := IH) f ρ hρ).symm x := by
  obtain ⟨z, rfl⟩ := (homeomorph H _).surjective x; simp [pullbackHomeomorph_symm_apply]
end Pullback
end TauCeti.PrincipalBundle.Extend
