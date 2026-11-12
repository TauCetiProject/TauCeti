/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.Geometry.Manifold.FiberBundle.Associated.Principal
public import TauCeti.Geometry.Manifold.FiberBundle.Associated.Pullback
public import TauCeti.Geometry.Manifold.FiberBundle.Principal.Classification
public import TauCeti.Topology.FiberBundle.Principal.Extension

/-!
# Smooth extension of the structure group of a principal bundle

Let `P` be a `C^n` principal `G`-bundle over a manifold `B` modelled on `IB`, and let `ρ : G →* H`
be a `C^n` homomorphism of Lie groups (more generally, into a group `H` modelled on `IH` with `C^n`
multiplication). The extended principal `H`-bundle `TauCeti.PrincipalBundle.Extend P ρ hρ`
(`P ×_ρ H`) has transition functions `b ↦ ρ (e.coordChange e' b 1)`, so it is a `C^n` fibre bundle
(`TauCeti.PrincipalBundle.Extend.contMDiffFiberBundle`).

In the charts through the fibre (`TauCeti.ManifoldTotalSpace`), the quotient map `(p, h) ↦ [p, h]`
and the canonical `ρ`-equivariant morphism `p ↦ [p, 1]` are `C^n`
(`ContMDiffWithinAt.totalSpaceMk_extendMk`,
`TauCeti.PrincipalBundle.Extend.contMDiff_totalSpaceMk_mk`,
`TauCeti.PrincipalBundle.Extend.contMDiff_inl`). Moreover:

* **Universal property and reduction recovery**
  (`TauCeti.PrincipalBundle.Extend.diffeomorphOfEquivariant`): when `H` is a `C^n` Lie group, any
  `C^n` `ρ`-equivariant map `φ : P → Q` into a principal `H`-bundle `Q` over `B` extends to a `C^n`
  `H`-equivariant diffeomorphism `(P ×_ρ H) ≃ₘ^n Q` over `B`. In particular, extending a `C^n`
  reduction or principal lift along `ρ` recovers `Q` up to canonical `C^n` diffeomorphism.
* **Functoriality, pullback, and associated bundles**: the canonical homeomorphisms for
  homomorphism congruence (`congrDiffeomorph`), identity (`idDiffeomorph`), composition
  (`compDiffeomorph`), base change (`pullbackDiffeomorph`), and associated bundles
  (`associatedDiffeomorph`, identifying `(P ×_ρ H) ×_H F ≃ₘ^n P ×_G F`) preserve local fibre
  coordinates in preferred charts and are therefore `C^n` diffeomorphisms.
* **Nonabelian Čech `H¹` compatibility** (`TauCeti.PrincipalBundle.Extend.mk_coordChange_eq_map`):
  on any cover indexed by preferred charts, the transition cocycle class of `Extend P ρ hρ` in
  `TauCeti.NonabelianCechH1` is `NonabelianCechH1.map ρ` applied to the transition cocycle class of
  `P`.
* **Commutative Lie groups** (`Dual` and `ZPow`): for a commutative `C^n` Lie group `A` (such as the
  circle), the dual bundle `Dual A Q` and `k`-th power bundle `ZPow A Q k` are `C^n` principal
  `A`-bundles whose Čech `H¹` classes are the inverse and `k`-th power of the class of `Q`
  (`mk_coordChange_dual`, `mk_coordChange_zpow`), and the canonical topological identifications lift
  to `C^n` diffeomorphisms (`dualDualDiffeomorph`, `zpowMulDiffeomorph`, `zpowNegOneDiffeomorph`,
  `diagMulZPowTwoDiffeomorph`).

## References

* S. Kobayashi, K. Nomizu, *Foundations of Differential Geometry I*, Interscience, 1963,
  Chapter I, §5 (extension and reduction of the structure group of a principal bundle).
* I. Kolář, P. W. Michor, J. Slovák, *Natural Operations in Differential Geometry*, Springer,
  1993, §§10.5–10.7 (homomorphisms of principal bundles and associated bundles).
-/

public section

noncomputable section

open Bundle Filter MulOpposite Set TauCeti TauCeti.PrincipalBundle
open scoped Manifold ContDiff Topology

/-! ### Smooth bundle structure and smoothness of classes -/

section SmoothExtend

variable {n : ℕ∞ω} {𝕜 B G H M : Type*} [NontriviallyNormedField 𝕜]
  {EB : Type*} [NormedAddCommGroup EB] [NormedSpace 𝕜 EB] {HB : Type*} [TopologicalSpace HB]
  {IB : ModelWithCorners 𝕜 EB HB} [TopologicalSpace B] [ChartedSpace HB B]
  {EG : Type*} [NormedAddCommGroup EG] [NormedSpace 𝕜 EG] {HG : Type*} [TopologicalSpace HG]
  {IG : ModelWithCorners 𝕜 EG HG} [Group G] [TopologicalSpace G] [ChartedSpace HG G]
  {EH : Type*} [NormedAddCommGroup EH] [NormedSpace 𝕜 EH] {HH : Type*} [TopologicalSpace HH]
  {IH : ModelWithCorners 𝕜 EH HH} [Group H] [TopologicalSpace H] [ChartedSpace HH H]
  {EM : Type*} [NormedAddCommGroup EM] [NormedSpace 𝕜 EM] {HM : Type*} [TopologicalSpace HM]
  {IM : ModelWithCorners 𝕜 EM HM} [TopologicalSpace M] [ChartedSpace HM M]
  {P : B → Type*} [TopologicalSpace (TotalSpace G P)] [∀ b, TopologicalSpace (P b)]
  [FiberBundle G P] [∀ b, MulAction Gᵐᵒᵖ (P b)] [PrincipalBundle G P]

variable (IG) in
/-- **Smooth structure-group extension.** When `P` is a `C^n` principal `G`-bundle, `H` has `C^n`
multiplication, and `ρ : G →* H` is `C^n`, the extended principal `H`-bundle `Extend P ρ hρ` is a
`C^n` fibre bundle. As for `AssociatedBundle.contMDiffFiberBundle`, the model `IG` does not appear
in the conclusion, so this is a theorem rather than a global instance. -/
theorem TauCeti.PrincipalBundle.Extend.contMDiffFiberBundle [ContinuousMul H]
    [ContMDiffMul IH n H] [hP : ContMDiffFiberBundle n G P IB IG] {ρ : G →* H} {hρ : Continuous ρ}
    (hρ' : ContMDiff IG IH n ρ) :
    ContMDiffFiberBundle n H (Extend P ρ hρ) IB IH := by
  refine (TauCeti.PrincipalBundle.contMDiffFiberBundle_iff n H IB IH (Extend P ρ hρ)).2
    fun e e' he he' ↦ ?_
  obtain ⟨b, rfl⟩ := he.out
  obtain ⟨b', rfl⟩ := he'.out
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

variable {ρ : G →* H} {f : M → B} {p : ∀ x, P (f x)} {h : M → H} {s : Set M} {x₀ : M}

/-- **Classes in an extended principal bundle depend `C^n`-smoothly on the pair**, within a set at a
point, for the charts through the fibre. -/
theorem ContMDiffWithinAt.totalSpaceMk_extendMk [ContinuousMul H] [ContMDiffMul IH n H]
    (hρ : Continuous ρ)
    (hp : ContMDiffWithinAt IM (IB.prod IG) n
      (fun x ↦ ManifoldTotalSpace.homeomorph G P ⟨f x, p x⟩) s x₀)
    (hh : ContMDiffWithinAt IM IH n h s x₀) (hρ' : ContMDiff IG IH n ρ) :
    ContMDiffWithinAt IM (IB.prod IH) n
      (fun x ↦ ManifoldTotalSpace.homeomorph H (Extend P ρ hρ)
        ⟨f x, Extend.mk ρ hρ (p x) (h x)⟩) s x₀ := by
  rw [ManifoldTotalSpace.contMDiffWithinAt_iff] at hp ⊢
  obtain ⟨hf, hp⟩ := hp
  refine ⟨hf, ?_⟩
  have hx₀ := mem_baseSet_trivializationAt G P (f x₀)
  refine ((hρ'.contMDiffAt.comp_contMDiffWithinAt x₀ hp).mul hh).congr_of_eventuallyEq ?_
    (Extend.trivializationAt_mk_snd ρ hρ hx₀ _ _)
  filter_upwards [hf.continuousWithinAt
    ((trivializationAt G P (f x₀)).open_baseSet.mem_nhds hx₀)] with x hx
  exact Extend.trivializationAt_mk_snd ρ hρ hx _ _

/-- The class `[p x, h x]` in `Extend P ρ hρ` is `C^n` at `x₀` when `⟨f x, p x⟩` and `h x` are. -/
theorem ContMDiffAt.totalSpaceMk_extendMk [ContinuousMul H] [ContMDiffMul IH n H]
    (hρ : Continuous ρ)
    (hp : ContMDiffAt IM (IB.prod IG) n
      (fun x ↦ ManifoldTotalSpace.homeomorph G P ⟨f x, p x⟩) x₀)
    (hh : ContMDiffAt IM IH n h x₀) (hρ' : ContMDiff IG IH n ρ) :
    ContMDiffAt IM (IB.prod IH) n
      (fun x ↦ ManifoldTotalSpace.homeomorph H (Extend P ρ hρ)
        ⟨f x, Extend.mk ρ hρ (p x) (h x)⟩) x₀ :=
  ContMDiffWithinAt.totalSpaceMk_extendMk hρ hp hh hρ'

/-- The class `[p x, h x]` in `Extend P ρ hρ` is `C^n` on `s` when `⟨f x, p x⟩` and `h x` are. -/
theorem ContMDiffOn.totalSpaceMk_extendMk [ContinuousMul H] [ContMDiffMul IH n H]
    (hρ : Continuous ρ)
    (hp : ContMDiffOn IM (IB.prod IG) n
      (fun x ↦ ManifoldTotalSpace.homeomorph G P ⟨f x, p x⟩) s)
    (hh : ContMDiffOn IM IH n h s) (hρ' : ContMDiff IG IH n ρ) :
    ContMDiffOn IM (IB.prod IH) n
      (fun x ↦ ManifoldTotalSpace.homeomorph H (Extend P ρ hρ)
        ⟨f x, Extend.mk ρ hρ (p x) (h x)⟩) s :=
  fun x hx ↦ (hp x hx).totalSpaceMk_extendMk hρ (hh x hx) hρ'

/-- The class `[p x, h x]` in `Extend P ρ hρ` is `C^n` when `⟨f x, p x⟩` and `h x` are. -/
theorem ContMDiff.totalSpaceMk_extendMk [ContinuousMul H] [ContMDiffMul IH n H]
    (hρ : Continuous ρ)
    (hp : ContMDiff IM (IB.prod IG) n fun x ↦ ManifoldTotalSpace.homeomorph G P ⟨f x, p x⟩)
    (hh : ContMDiff IM IH n h) (hρ' : ContMDiff IG IH n ρ) :
    ContMDiff IM (IB.prod IH) n fun x ↦
      ManifoldTotalSpace.homeomorph H (Extend P ρ hρ) ⟨f x, Extend.mk ρ hρ (p x) (h x)⟩ :=
  fun x ↦ (hp x).totalSpaceMk_extendMk hρ (hh x) hρ'

namespace TauCeti.PrincipalBundle.Extend

/-- The quotient map `(p, h) ↦ [p, h]` from `P × H` onto `Extend P ρ hρ` is `C^n` in the charts
through the fibre. -/
theorem contMDiff_totalSpaceMk_mk [ContinuousMul H] [ContMDiffMul IH n H]
    {ρ : G →* H} (hρ : Continuous ρ) (hρ' : ContMDiff IG IH n ρ) :
    ContMDiff ((IB.prod IG).prod IH) (IB.prod IH) n
      (fun x : ManifoldTotalSpace G P × H ↦
        ManifoldTotalSpace.homeomorph H (Extend P ρ hρ)
          ⟨((ManifoldTotalSpace.homeomorph G P).symm x.1).proj,
            mk ρ hρ ((ManifoldTotalSpace.homeomorph G P).symm x.1).2 x.2⟩) := by
  have hp : ContMDiff ((IB.prod IG).prod IH) (IB.prod IG) n
      (fun x : ManifoldTotalSpace G P × H ↦
        ManifoldTotalSpace.homeomorph G P
          ⟨((ManifoldTotalSpace.homeomorph G P).symm x.1).proj,
            ((ManifoldTotalSpace.homeomorph G P).symm x.1).2⟩) :=
    contMDiff_fst.congr fun x ↦ by simp only [TotalSpace.eta, Homeomorph.apply_symm_apply]
  exact hp.totalSpaceMk_extendMk hρ contMDiff_snd hρ'

/-- The canonical `ρ`-equivariant map `p ↦ [p, 1]` from `P` to `Extend P ρ hρ` is `C^n` in the
charts through the fibre. -/
theorem contMDiff_inl [ContinuousMul H] [ContMDiffMul IH n H]
    {ρ : G →* H} (hρ : Continuous ρ) (hρ' : ContMDiff IG IH n ρ) :
    ContMDiff (IB.prod IG) (IB.prod IH) n
      (fun x : ManifoldTotalSpace G P ↦
        ManifoldTotalSpace.homeomorph H (Extend P ρ hρ)
          ⟨((ManifoldTotalSpace.homeomorph G P).symm x).proj,
            inl ρ hρ ((ManifoldTotalSpace.homeomorph G P).symm x).2⟩) := by
  have hp : ContMDiff (IB.prod IG) (IB.prod IG) n
      (fun x : ManifoldTotalSpace G P ↦
        ManifoldTotalSpace.homeomorph G P
          ⟨((ManifoldTotalSpace.homeomorph G P).symm x).proj,
            ((ManifoldTotalSpace.homeomorph G P).symm x).2⟩) :=
    contMDiff_id.congr fun x ↦ by simp only [TotalSpace.eta, Homeomorph.apply_symm_apply, id_eq]
  simpa only [inl_def] using hp.totalSpaceMk_extendMk hρ contMDiff_const hρ'

end TauCeti.PrincipalBundle.Extend

end SmoothExtend

/-! ### Smooth universal property and reduction / lift recovery -/

namespace TauCeti.PrincipalBundle.Extend

section ReductionDiffeomorph

variable {n : ℕ∞ω} {𝕜 B G H : Type*} [NontriviallyNormedField 𝕜]
  {EB : Type*} [NormedAddCommGroup EB] [NormedSpace 𝕜 EB] {HB : Type*} [TopologicalSpace HB]
  {IB : ModelWithCorners 𝕜 EB HB} [TopologicalSpace B] [ChartedSpace HB B]
  {EG : Type*} [NormedAddCommGroup EG] [NormedSpace 𝕜 EG] {HG : Type*} [TopologicalSpace HG]
  {IG : ModelWithCorners 𝕜 EG HG} [Group G] [TopologicalSpace G] [ChartedSpace HG G]
  {EH : Type*} [NormedAddCommGroup EH] [NormedSpace 𝕜 EH] {HH : Type*} [TopologicalSpace HH]
  {IH : ModelWithCorners 𝕜 EH HH} [Group H] [TopologicalSpace H] [ChartedSpace HH H]
  [ContinuousMul H] [LieGroup IH n H]
  {P : B → Type*} [TopologicalSpace (TotalSpace G P)] [∀ b, TopologicalSpace (P b)]
  [FiberBundle G P] [∀ b, MulAction Gᵐᵒᵖ (P b)] [PrincipalBundle G P]
  {Q : B → Type*} [TopologicalSpace (TotalSpace H Q)] [∀ b, TopologicalSpace (Q b)]
  [FiberBundle H Q] [∀ b, MulAction Hᵐᵒᵖ (Q b)] [PrincipalBundle H Q]

/-- **Smooth universal property and reduction recovery.** Let `H` be a `C^n` Lie group and let
`φ : ∀ b, P b → Q b` be a `ρ`-equivariant map whose total-space map is `C^n`. Then
`[p, h] ↦ φ b p • h` defines a `C^n` `H`-equivariant diffeomorphism
`ManifoldTotalSpace H (Extend P ρ hρ) ≃ₘ^n ManifoldTotalSpace H Q` over `B`. -/
def diffeomorphOfEquivariant (ρ : G →* H) (hρ : Continuous ρ)
    (φ : ∀ b, P b → Q b)
    (hφ : ∀ b (p : P b) (g : G), φ b (op g • p) = op (ρ g) • φ b p)
    (hφc : ContMDiff (IB.prod IG) (IB.prod IH) n
      (fun x : ManifoldTotalSpace G P ↦
        ManifoldTotalSpace.homeomorph H Q
          ⟨((ManifoldTotalSpace.homeomorph G P).symm x).proj,
            φ _ ((ManifoldTotalSpace.homeomorph G P).symm x).2⟩)) :
    ManifoldTotalSpace H (Extend P ρ hρ) ≃ₘ^n⟮IB.prod IH, IB.prod IH⟯ ManifoldTotalSpace H Q :=
  PrincipalBundle.diffeomorphOfEquivariant H
    (fun b ↦ equivOfEquivariant ρ hρ φ hφ b)
    (equivOfEquivariant_smul ρ hρ φ hφ) <| by
    have (b : B) : Nonempty (P b) := ⟨(FiberBundle.homeomorphAt G P b).symm 1⟩
    intro x₀
    let b₀ := ((ManifoldTotalSpace.homeomorph H (Extend P ρ hρ)).symm x₀).proj
    let eP := trivializationAt G P b₀
    have hbP₀ : b₀ ∈ eP.baseSet := mem_baseSet_trivializationAt G P b₀
    let σ : ∀ b, P b := fun b ↦ eP.symm b 1
    have hσ : ContMDiffAt IB (IB.prod IG) n
        (fun b ↦ ManifoldTotalSpace.homeomorph G P ⟨b, σ b⟩) b₀ :=
      ManifoldTotalSpace.contMDiffAt_totalSpaceMk_trivializationAt_symm b₀ 1
    have hφσ_base : ContMDiffAt IB (IB.prod IH) n
        (fun b ↦ ManifoldTotalSpace.homeomorph H Q ⟨b, φ b (σ b)⟩) b₀ :=
      (hφc.contMDiffAt.comp b₀ hσ).congr_of_eventuallyEq
        (.of_forall fun b ↦ by dsimp only [Function.comp_def]; rw [Homeomorph.symm_apply_apply])
    have hπ := ManifoldTotalSpace.contMDiff_proj n H (Extend P ρ hρ) IB IH x₀
    have hφσ := hφσ_base.comp x₀ hπ
    have hh := ManifoldTotalSpace.contMDiffAt_trivializationAt_snd n IB IH x₀
    refine (hφσ.totalSpaceMk_smul hh).congr_of_eventuallyEq ?_
    filter_upwards [hπ.continuousAt.preimage_mem_nhds (eP.open_baseSet.mem_nhds hbP₀)] with y hy
    obtain ⟨⟨b, z⟩, rfl⟩ := (ManifoldTotalSpace.homeomorph H (Extend P ρ hρ)).surjective y
    have hbP : b ∈ eP.baseSet := by simpa using hy
    rw [ManifoldTotalSpace.fiberwiseMap_homeomorph]
    change _ = ManifoldTotalSpace.homeomorph H Q
      ⟨((ManifoldTotalSpace.homeomorph H _).symm (ManifoldTotalSpace.homeomorph H _ ⟨b, z⟩)).proj,
        op _ • φ _ (σ _)⟩
    rw [Homeomorph.symm_apply_apply]
    change ManifoldTotalSpace.homeomorph H Q ⟨b, equivOfEquivariant ρ hρ φ hφ b z⟩ =
      ManifoldTotalSpace.homeomorph H Q
        ⟨b, op (trivializationAt H (Extend P ρ hρ) b₀ ⟨b, z⟩).2 • φ b (σ b)⟩
    apply congrArg (fun w ↦ ManifoldTotalSpace.homeomorph H Q ⟨b, w⟩)
    obtain ⟨h, rfl⟩ := (mk_bijective ρ hρ (σ b)).surjective z
    have hσ1 : (eP ⟨b, σ b⟩).2 = 1 := congrArg Prod.snd (eP.apply_mk_symm hbP 1)
    rw [equivOfEquivariant_mk, trivializationAt_mk_snd ρ hρ hbP, hσ1, map_one, one_mul]

section

variable (ρ : G →* H) (hρ : Continuous ρ) (φ : ∀ b, P b → Q b)
  (hφ : ∀ b (p : P b) (g : G), φ b (op g • p) = op (ρ g) • φ b p)
  (hφc : ContMDiff (IB.prod IG) (IB.prod IH) n
    (fun x : ManifoldTotalSpace G P ↦
      ManifoldTotalSpace.homeomorph H Q
        ⟨((ManifoldTotalSpace.homeomorph G P).symm x).proj,
          φ _ ((ManifoldTotalSpace.homeomorph G P).symm x).2⟩))

@[simp]
theorem diffeomorphOfEquivariant_apply (z : TotalSpace H (Extend P ρ hρ)) :
    diffeomorphOfEquivariant (IB := IB) (IG := IG) (IH := IH) ρ hρ φ hφ hφc
        (ManifoldTotalSpace.homeomorph H _ z) =
      ManifoldTotalSpace.homeomorph H Q ⟨z.proj, equivOfEquivariant ρ hρ φ hφ z.proj z.2⟩ :=
  PrincipalBundle.diffeomorphOfEquivariant_apply _ _ _ z

@[simp]
theorem diffeomorphOfEquivariant_symm_apply (q : TotalSpace H Q) :
    (diffeomorphOfEquivariant (IB := IB) (IG := IG) (IH := IH) ρ hρ φ hφ hφc).symm
        (ManifoldTotalSpace.homeomorph H Q q) =
      ManifoldTotalSpace.homeomorph H _ ⟨q.proj, (equivOfEquivariant ρ hρ φ hφ q.proj).symm q.2⟩ :=
  PrincipalBundle.diffeomorphOfEquivariant_symm_apply _ _ _ q

@[simp]
theorem diffeomorphOfEquivariant_mk {b : B} (p : P b) (h : H) :
    diffeomorphOfEquivariant (IB := IB) (IG := IG) (IH := IH) ρ hρ φ hφ hφc
        (ManifoldTotalSpace.homeomorph H _ ⟨b, mk ρ hρ p h⟩) =
      ManifoldTotalSpace.homeomorph H Q ⟨b, op h • φ b p⟩ := by
  rw [diffeomorphOfEquivariant_apply, equivOfEquivariant_mk]

@[simp]
theorem diffeomorphOfEquivariant_inl {b : B} (p : P b) :
    diffeomorphOfEquivariant (IB := IB) (IG := IG) (IH := IH) ρ hρ φ hφ hφc
        (ManifoldTotalSpace.homeomorph H _ ⟨b, inl ρ hρ p⟩) =
      ManifoldTotalSpace.homeomorph H Q ⟨b, φ b p⟩ := by
  rw [diffeomorphOfEquivariant_apply, equivOfEquivariant_inl]

theorem diffeomorphOfEquivariant_op_smul (h' : H) (x : ManifoldTotalSpace H (Extend P ρ hρ)) :
    diffeomorphOfEquivariant (IB := IB) (IG := IG) (IH := IH) ρ hρ φ hφ hφc (op h' • x) =
      op h' • diffeomorphOfEquivariant (IB := IB) (IG := IG) (IH := IH) ρ hρ φ hφ hφc x :=
  PrincipalBundle.diffeomorphOfEquivariant_op_smul _ _ _ h' x

end

end ReductionDiffeomorph

/-! ### Functoriality, pullback, and associated-bundle diffeomorphisms -/

section ChartPreserving

variable {n : ℕ∞ω} {𝕜 B G : Type*} [NontriviallyNormedField 𝕜]
  {EB : Type*} [NormedAddCommGroup EB] [NormedSpace 𝕜 EB] {HB : Type*} [TopologicalSpace HB]
  {IB : ModelWithCorners 𝕜 EB HB} [TopologicalSpace B] [ChartedSpace HB B]
  [Group G] [TopologicalSpace G]
  {P : B → Type*} [TopologicalSpace (TotalSpace G P)] [∀ b, TopologicalSpace (P b)]
  [FiberBundle G P] [∀ b, MulAction Gᵐᵒᵖ (P b)] [PrincipalBundle G P]

/-- Helper constructing a `C^n` diffeomorphism of charted total spaces from a fibrewise equivalence
that preserves local fibre coordinates over the base sets of `trivializationAt G P`. -/
private def diffeomorphOfCoordEq
    {F : Type*} {EF : Type*} [NormedAddCommGroup EF] [NormedSpace 𝕜 EF]
    {HF : Type*} [TopologicalSpace HF] {IF : ModelWithCorners 𝕜 EF HF}
    [TopologicalSpace F] [ChartedSpace HF F]
    {E₁ E₂ : B → Type*}
    [TopologicalSpace (TotalSpace F E₁)] [∀ b, TopologicalSpace (E₁ b)] [FiberBundle F E₁]
    [TopologicalSpace (TotalSpace F E₂)] [∀ b, TopologicalSpace (E₂ b)] [FiberBundle F E₂]
    (e : ∀ b, E₁ b ≃ E₂ b)
    (hcoord : ∀ {b' b : B}, b ∈ (trivializationAt G P b').baseSet → ∀ z : E₁ b,
      (trivializationAt F E₁ b' ⟨b, z⟩).2 = (trivializationAt F E₂ b' ⟨b, e b z⟩).2) :
    ManifoldTotalSpace F E₁ ≃ₘ^n⟮IB.prod IF, IB.prod IF⟯ ManifoldTotalSpace F E₂ where
  toFun := ManifoldTotalSpace.fiberwiseMap fun b ↦ e b
  invFun := ManifoldTotalSpace.fiberwiseMap fun b ↦ (e b).symm
  left_inv z := by
    obtain ⟨z, rfl⟩ := (ManifoldTotalSpace.homeomorph F E₁).surjective z
    simp
  right_inv z := by
    obtain ⟨z, rfl⟩ := (ManifoldTotalSpace.homeomorph F E₂).surjective z
    simp
  contMDiff_toFun := by
    change ContMDiff (IB.prod IF) (IB.prod IF) n (ManifoldTotalSpace.fiberwiseMap fun b ↦ e b)
    intro x₀
    have hf_eq : ManifoldTotalSpace.fiberwiseMap (fun b ↦ e b) =
        fun y : ManifoldTotalSpace F E₁ ↦
          ManifoldTotalSpace.homeomorph F E₂
            ⟨((ManifoldTotalSpace.homeomorph F E₁).symm y).proj,
              e _ ((ManifoldTotalSpace.homeomorph F E₁).symm y).2⟩ := by
      funext y
      obtain ⟨z, rfl⟩ := (ManifoldTotalSpace.homeomorph F E₁).surjective y
      rw [ManifoldTotalSpace.fiberwiseMap_homeomorph, Homeomorph.symm_apply_apply]
    rw [hf_eq, ManifoldTotalSpace.contMDiffAt_iff]
    let b₀ := ((ManifoldTotalSpace.homeomorph F E₁).symm x₀).proj
    have hb₀ : b₀ ∈ (trivializationAt G P b₀).baseSet := mem_baseSet_trivializationAt G P b₀
    have hπ := ManifoldTotalSpace.contMDiff_proj n F E₁ IB IF x₀
    have hv := ManifoldTotalSpace.contMDiffAt_trivializationAt_snd n IB IF x₀
    refine ⟨hπ, hv.congr_of_eventuallyEq ?_⟩
    filter_upwards [hπ.continuousAt.preimage_mem_nhds
      ((trivializationAt G P b₀).open_baseSet.mem_nhds hb₀)] with y hy
    obtain ⟨⟨b, z⟩, rfl⟩ := (ManifoldTotalSpace.homeomorph F E₁).surjective y
    have hb : b ∈ (trivializationAt G P b₀).baseSet := by simpa using hy
    change (trivializationAt F E₂ b₀
        ⟨((ManifoldTotalSpace.homeomorph F E₁).symm
            (ManifoldTotalSpace.homeomorph F E₁ ⟨b, z⟩)).proj,
          e _ ((ManifoldTotalSpace.homeomorph F E₁).symm
            (ManifoldTotalSpace.homeomorph F E₁ ⟨b, z⟩)).2⟩).2 =
      (trivializationAt F E₁ b₀
        ((ManifoldTotalSpace.homeomorph F E₁).symm
          (ManifoldTotalSpace.homeomorph F E₁ ⟨b, z⟩))).2
    rw [Homeomorph.symm_apply_apply]
    exact (hcoord hb z).symm
  contMDiff_invFun := by
    change ContMDiff (IB.prod IF) (IB.prod IF) n
      (ManifoldTotalSpace.fiberwiseMap fun b ↦ (e b).symm)
    intro x₀
    have hf_eq : ManifoldTotalSpace.fiberwiseMap (fun b ↦ (e b).symm) =
        fun y : ManifoldTotalSpace F E₂ ↦
          ManifoldTotalSpace.homeomorph F E₁
            ⟨((ManifoldTotalSpace.homeomorph F E₂).symm y).proj,
              (e _).symm ((ManifoldTotalSpace.homeomorph F E₂).symm y).2⟩ := by
      funext y
      obtain ⟨z, rfl⟩ := (ManifoldTotalSpace.homeomorph F E₂).surjective y
      rw [ManifoldTotalSpace.fiberwiseMap_homeomorph, Homeomorph.symm_apply_apply]
    rw [hf_eq, ManifoldTotalSpace.contMDiffAt_iff]
    let b₀ := ((ManifoldTotalSpace.homeomorph F E₂).symm x₀).proj
    have hb₀ : b₀ ∈ (trivializationAt G P b₀).baseSet := mem_baseSet_trivializationAt G P b₀
    have hπ := ManifoldTotalSpace.contMDiff_proj n F E₂ IB IF x₀
    have hv := ManifoldTotalSpace.contMDiffAt_trivializationAt_snd n IB IF x₀
    refine ⟨hπ, hv.congr_of_eventuallyEq ?_⟩
    filter_upwards [hπ.continuousAt.preimage_mem_nhds
      ((trivializationAt G P b₀).open_baseSet.mem_nhds hb₀)] with y hy
    obtain ⟨⟨b, w⟩, rfl⟩ := (ManifoldTotalSpace.homeomorph F E₂).surjective y
    have hb : b ∈ (trivializationAt G P b₀).baseSet := by simpa using hy
    change (trivializationAt F E₁ b₀
        ⟨((ManifoldTotalSpace.homeomorph F E₂).symm
            (ManifoldTotalSpace.homeomorph F E₂ ⟨b, w⟩)).proj,
          (e _).symm ((ManifoldTotalSpace.homeomorph F E₂).symm
            (ManifoldTotalSpace.homeomorph F E₂ ⟨b, w⟩)).2⟩).2 =
      (trivializationAt F E₂ b₀
        ((ManifoldTotalSpace.homeomorph F E₂).symm
          (ManifoldTotalSpace.homeomorph F E₂ ⟨b, w⟩))).2
    rw [Homeomorph.symm_apply_apply]
    simpa only [Equiv.apply_symm_apply] using hcoord hb ((e b).symm w)

/-! #### Congruence in the homomorphism -/

section Congr

variable {H : Type*} {EH : Type*} [NormedAddCommGroup EH] [NormedSpace 𝕜 EH]
  {HH : Type*} [TopologicalSpace HH] {IH : ModelWithCorners 𝕜 EH HH}
  [Group H] [TopologicalSpace H] [ContinuousMul H] [ChartedSpace HH H]
  {ρ₁ ρ₂ : G →* H}

/-- Equal homomorphisms produce canonically `C^n`-diffeomorphic extended total spaces. -/
def congrDiffeomorph (h : ρ₁ = ρ₂) (hρ₁ : Continuous ρ₁) (hρ₂ : Continuous ρ₂) :
    ManifoldTotalSpace H (Extend P ρ₁ hρ₁) ≃ₘ^n⟮IB.prod IH, IB.prod IH⟯
      ManifoldTotalSpace H (Extend P ρ₂ hρ₂) :=
  diffeomorphOfCoordEq (G := G) (P := P) (fun b ↦ congrEquiv h hρ₁ hρ₂ b) fun _ z ↦
    trivializationAt_congrEquiv_snd h hρ₁ hρ₂ _ _ z

@[simp]
theorem congrDiffeomorph_apply (h : ρ₁ = ρ₂) (hρ₁ : Continuous ρ₁) (hρ₂ : Continuous ρ₂)
    (z : TotalSpace H (Extend P ρ₁ hρ₁)) :
    congrDiffeomorph (n := n) (IB := IB) (IH := IH) (G := G) (P := P) h hρ₁ hρ₂
        (ManifoldTotalSpace.homeomorph H _ z) =
      ManifoldTotalSpace.homeomorph H _ (congrHomeomorph (P := P) h hρ₁ hρ₂ z) := by
  rw [congrHomeomorph_apply]
  exact ManifoldTotalSpace.fiberwiseMap_homeomorph (E' := Extend P ρ₂ hρ₂) _ z

@[simp]
theorem congrDiffeomorph_mk (h : ρ₁ = ρ₂) (hρ₁ : Continuous ρ₁) (hρ₂ : Continuous ρ₂)
    {b : B} (p : P b) (x : H) :
    congrDiffeomorph (n := n) (IB := IB) (IH := IH) (G := G) (P := P) h hρ₁ hρ₂
        (ManifoldTotalSpace.homeomorph H _ ⟨b, mk ρ₁ hρ₁ p x⟩) =
      ManifoldTotalSpace.homeomorph H _ ⟨b, mk ρ₂ hρ₂ p x⟩ := by
  rw [congrDiffeomorph_apply, congrHomeomorph_apply, congrEquiv_mk]

end Congr

/-! #### Extension along the identity homomorphism -/

section Id

variable {EG : Type*} [NormedAddCommGroup EG] [NormedSpace 𝕜 EG]
  {HG : Type*} [TopologicalSpace HG] {IG : ModelWithCorners 𝕜 EG HG}
  [ContinuousMul G] [ChartedSpace HG G]

/-- **Smooth identity extension.** `Extend P (MonoidHom.id G) continuous_id` is canonically `C^n`
diffeomorphic to `P` over `B` in the charts through the fibre. -/
def idDiffeomorph :
    ManifoldTotalSpace G (Extend P (MonoidHom.id G) continuous_id)
      ≃ₘ^n⟮IB.prod IG, IB.prod IG⟯ ManifoldTotalSpace G P :=
  diffeomorphOfCoordEq (G := G) (P := P) idEquiv trivializationAt_idEquiv_snd

@[simp]
theorem idDiffeomorph_apply (z : TotalSpace G (Extend P (MonoidHom.id G) continuous_id)) :
    idDiffeomorph (n := n) (IB := IB) (IG := IG) (G := G) (P := P)
        (ManifoldTotalSpace.homeomorph G _ z) =
      ManifoldTotalSpace.homeomorph G P (idHomeomorph z) := by
  rw [idHomeomorph_apply]
  exact ManifoldTotalSpace.fiberwiseMap_homeomorph _ z

@[simp]
theorem idDiffeomorph_symm_apply (z : TotalSpace G P) :
    (idDiffeomorph (n := n) (IB := IB) (IG := IG) (G := G) (P := P)).symm
        (ManifoldTotalSpace.homeomorph G P z) =
      ManifoldTotalSpace.homeomorph G _ ((idHomeomorph (G := G) (P := P)).symm z) := by
  rw [idHomeomorph_symm_apply, ← idEquiv_symm_apply]
  exact ManifoldTotalSpace.fiberwiseMap_homeomorph _ z

@[simp]
theorem idDiffeomorph_mk {b : B} (p : P b) (g : G) :
    idDiffeomorph (n := n) (IB := IB) (IG := IG) (G := G) (P := P)
        (ManifoldTotalSpace.homeomorph G _ ⟨b, mk (MonoidHom.id G) continuous_id p g⟩) =
      ManifoldTotalSpace.homeomorph G P ⟨b, op g • p⟩ := by
  rw [idDiffeomorph_apply, idHomeomorph_mk]

end Id

/-! #### Composition of extensions -/

section Comp

variable {H K : Type*} [Group H] [TopologicalSpace H] [ContinuousMul H]
  {EK : Type*} [NormedAddCommGroup EK] [NormedSpace 𝕜 EK]
  {HK : Type*} [TopologicalSpace HK] {IK : ModelWithCorners 𝕜 EK HK}
  [Group K] [TopologicalSpace K] [ContinuousMul K] [ChartedSpace HK K]
  (ρ : G →* H) (hρ : Continuous ρ) (σ : H →* K) (hσ : Continuous σ)

/-- **Smooth functoriality of structure-group extension under composition.** Extending `P` along `ρ`
and then along `σ` is canonically `C^n` diffeomorphic over `B` to extending `P` along `σ.comp ρ`. No
manifold structure on the intermediate group `H` is required to state or prove the diffeomorphism in
the `K`-charts. -/
def compDiffeomorph :
    ManifoldTotalSpace K (Extend (Extend P ρ hρ) σ hσ) ≃ₘ^n⟮IB.prod IK, IB.prod IK⟯
      ManifoldTotalSpace K (Extend P (σ.comp ρ) (hσ.comp hρ)) :=
  diffeomorphOfCoordEq (P := P) (compEquiv ρ hρ σ hσ) (trivializationAt_compEquiv_snd ρ hρ σ hσ)

@[simp]
theorem compDiffeomorph_apply (z : TotalSpace K (Extend (Extend P ρ hρ) σ hσ)) :
    compDiffeomorph (n := n) (IB := IB) (IK := IK) (P := P) ρ hρ σ hσ
        (ManifoldTotalSpace.homeomorph K _ z) =
      ManifoldTotalSpace.homeomorph K _ (compHomeomorph ρ hρ σ hσ z) := by
  rw [compHomeomorph_apply]
  exact ManifoldTotalSpace.fiberwiseMap_homeomorph _ z

@[simp]
theorem compDiffeomorph_symm_apply (z : TotalSpace K (Extend P (σ.comp ρ) (hσ.comp hρ))) :
    (compDiffeomorph (n := n) (IB := IB) (IK := IK) (P := P) ρ hρ σ hσ).symm
        (ManifoldTotalSpace.homeomorph K _ z) =
      ManifoldTotalSpace.homeomorph K _ ((compHomeomorph ρ hρ σ hσ).symm z) := by
  rw [compHomeomorph_symm_apply]
  exact ManifoldTotalSpace.fiberwiseMap_homeomorph _ z

@[simp]
theorem compDiffeomorph_mk {b : B} (p : P b) (h : H) (k : K) :
    compDiffeomorph (n := n) (IB := IB) (IK := IK) (P := P) ρ hρ σ hσ
        (ManifoldTotalSpace.homeomorph K _ ⟨b, mk σ hσ (mk ρ hρ p h) k⟩) =
      ManifoldTotalSpace.homeomorph K _ ⟨b, mk (σ.comp ρ) (hσ.comp hρ) p (σ h * k)⟩ := by
  rw [compDiffeomorph_apply, compHomeomorph_mk]

end Comp

/-! #### Associated bundles of an extended principal bundle -/

section Associated

variable {H F : Type*} [Group H] [TopologicalSpace H] [ContinuousMul H]
  {EF : Type*} [NormedAddCommGroup EF] [NormedSpace 𝕜 EF]
  {HF : Type*} [TopologicalSpace HF] {IF : ModelWithCorners 𝕜 EF HF}
  [TopologicalSpace F] [ChartedSpace HF F]
  [MulAction H F] [ContinuousSMul H F] [MulAction G F] [ContinuousSMul G F]

/-- **Smooth associated bundle of an extended principal bundle.** `(P ×_ρ H) ×_H F` is canonically
`C^n` diffeomorphic over `B` to `P ×_G F` in the charts through the fibre when `G` acts on `F`
through `ρ`. -/
def associatedDiffeomorph (ρ : G →* H) (hρ : Continuous ρ)
    (hF : ∀ (g : G) (v : F), g • v = ρ g • v) :
    ManifoldTotalSpace F (AssociatedBundle H (Extend P ρ hρ) F) ≃ₘ^n⟮IB.prod IF, IB.prod IF⟯
      ManifoldTotalSpace F (AssociatedBundle G P F) :=
  diffeomorphOfCoordEq (P := P) (associatedEquiv ρ hρ hF)
    (trivializationAt_associatedEquiv_snd ρ hρ hF)

@[simp]
theorem associatedDiffeomorph_apply (ρ : G →* H) (hρ : Continuous ρ)
    (hF : ∀ (g : G) (v : F), g • v = ρ g • v)
    (z : TotalSpace F (AssociatedBundle H (Extend P ρ hρ) F)) :
    associatedDiffeomorph (n := n) (IB := IB) (IF := IF) (P := P) ρ hρ hF
        (ManifoldTotalSpace.homeomorph F _ z) =
      ManifoldTotalSpace.homeomorph F _ (associatedHomeomorph ρ hρ hF z) := by
  rw [associatedHomeomorph_apply]
  exact ManifoldTotalSpace.fiberwiseMap_homeomorph _ z

@[simp]
theorem associatedDiffeomorph_symm_apply (ρ : G →* H) (hρ : Continuous ρ)
    (hF : ∀ (g : G) (v : F), g • v = ρ g • v) (z : TotalSpace F (AssociatedBundle G P F)) :
    (associatedDiffeomorph (n := n) (IB := IB) (IF := IF) (P := P) ρ hρ hF).symm
        (ManifoldTotalSpace.homeomorph F _ z) =
      ManifoldTotalSpace.homeomorph F _ ((associatedHomeomorph ρ hρ hF).symm z) := by
  rw [associatedHomeomorph_symm_apply]
  exact ManifoldTotalSpace.fiberwiseMap_homeomorph _ z

@[simp]
theorem associatedDiffeomorph_mk (ρ : G →* H) (hρ : Continuous ρ)
    (hF : ∀ (g : G) (v : F), g • v = ρ g • v) {b : B} (p : P b) (h : H) (v : F) :
    associatedDiffeomorph (n := n) (IB := IB) (IF := IF) (P := P) ρ hρ hF
        (ManifoldTotalSpace.homeomorph F _ ⟨b, AssociatedBundle.mk H (mk ρ hρ p h) v⟩) =
      ManifoldTotalSpace.homeomorph F _ ⟨b, AssociatedBundle.mk G p (h • v)⟩ := by
  rw [associatedDiffeomorph_apply, associatedHomeomorph_mk]

end Associated

end ChartPreserving

/-! #### Base change (pullback) -/

section Pullback

variable {n : ℕ∞ω} {𝕜 B B' G H : Type*} [NontriviallyNormedField 𝕜]
  [TopologicalSpace B]
  {EB' : Type*} [NormedAddCommGroup EB'] [NormedSpace 𝕜 EB'] {HB' : Type*} [TopologicalSpace HB']
  {IB' : ModelWithCorners 𝕜 EB' HB'} [TopologicalSpace B'] [ChartedSpace HB' B']
  {EH : Type*} [NormedAddCommGroup EH] [NormedSpace 𝕜 EH] {HH : Type*} [TopologicalSpace HH]
  {IH : ModelWithCorners 𝕜 EH HH} [Group H] [TopologicalSpace H] [ContinuousMul H]
  [ChartedSpace HH H]
  [Group G] [TopologicalSpace G]
  {P : B → Type*} [TopologicalSpace (TotalSpace G P)] [∀ b, TopologicalSpace (P b)]
  [FiberBundle G P] [∀ b, Nonempty (P b)] [∀ b, MulAction Gᵐᵒᵖ (P b)] [PrincipalBundle G P]
  {M : Type*} [FunLike M B' B] [ContinuousMapClass M B' B] (f : M)
  (ρ : G →* H) (hρ : Continuous ρ)

/-- **Smooth pullback comparison for structure-group extension.** Extending `f *ᵖ P` along `ρ` is
canonically `C^n` diffeomorphic over `B'` to pulling back `Extend P ρ hρ` along `f`. As for
`AssociatedBundle.pullbackDiffeomorph`, only continuity of `f` is needed for the chart
comparison. -/
def pullbackDiffeomorph :
    ManifoldTotalSpace H (Extend ((f : B' → B) *ᵖ P) ρ hρ) ≃ₘ^n⟮IB'.prod IH, IB'.prod IH⟯
      ManifoldTotalSpace H ((f : B' → B) *ᵖ (Extend P ρ hρ)) where
  toFun := ManifoldTotalSpace.fiberwiseMap fun x ↦ pullbackEquiv f ρ hρ x
  invFun := ManifoldTotalSpace.fiberwiseMap fun x ↦ (pullbackEquiv f ρ hρ x).symm
  left_inv z := by
    obtain ⟨z, rfl⟩ := (ManifoldTotalSpace.homeomorph H _).surjective z
    simp
  right_inv z := by
    obtain ⟨z, rfl⟩ := (ManifoldTotalSpace.homeomorph H _).surjective z
    simp
  contMDiff_toFun := by
    change ContMDiff (IB'.prod IH) (IB'.prod IH) n
      (ManifoldTotalSpace.fiberwiseMap fun x ↦ pullbackEquiv f ρ hρ x)
    intro y₀
    have hf_eq : ManifoldTotalSpace.fiberwiseMap (fun x ↦ pullbackEquiv f ρ hρ x) =
        fun y : ManifoldTotalSpace H (Extend ((f : B' → B) *ᵖ P) ρ hρ) ↦
          ManifoldTotalSpace.homeomorph H _
            ⟨((ManifoldTotalSpace.homeomorph H _).symm y).proj,
              pullbackEquiv f ρ hρ _ ((ManifoldTotalSpace.homeomorph H _).symm y).2⟩ := by
      funext y
      obtain ⟨z, rfl⟩ := (ManifoldTotalSpace.homeomorph H _).surjective y
      rw [ManifoldTotalSpace.fiberwiseMap_homeomorph, Homeomorph.symm_apply_apply]
    rw [hf_eq, ManifoldTotalSpace.contMDiffAt_iff]
    let x₀ := ((ManifoldTotalSpace.homeomorph H _).symm y₀).proj
    have hx₀ : f x₀ ∈ (trivializationAt G P (f x₀)).baseSet := mem_baseSet_trivializationAt G P _
    have hπ := ManifoldTotalSpace.contMDiff_proj n H (Extend ((f : B' → B) *ᵖ P) ρ hρ) IB' IH y₀
    have hv := ManifoldTotalSpace.contMDiffAt_trivializationAt_snd n IB' IH y₀
    refine ⟨hπ, hv.congr_of_eventuallyEq ?_⟩
    filter_upwards [((map_continuous f).continuousAt.comp hπ.continuousAt).preimage_mem_nhds
      ((trivializationAt G P (f x₀)).open_baseSet.mem_nhds hx₀)] with y hy
    obtain ⟨⟨x, z⟩, rfl⟩ := (ManifoldTotalSpace.homeomorph H _).surjective y
    have hx : f x ∈ (trivializationAt G P (f x₀)).baseSet := by simpa using hy
    change (trivializationAt H ((f : B' → B) *ᵖ (Extend P ρ hρ)) x₀
        ⟨((ManifoldTotalSpace.homeomorph H _).symm
            (ManifoldTotalSpace.homeomorph H _ ⟨x, z⟩)).proj,
          pullbackEquiv f ρ hρ _ ((ManifoldTotalSpace.homeomorph H _).symm
            (ManifoldTotalSpace.homeomorph H _ ⟨x, z⟩)).2⟩).2 =
      (trivializationAt H (Extend ((f : B' → B) *ᵖ P) ρ hρ) x₀
        ((ManifoldTotalSpace.homeomorph H _).symm
          (ManifoldTotalSpace.homeomorph H _ ⟨x, z⟩))).2
    rw [Homeomorph.symm_apply_apply]
    change (trivializationAt H ((f : B' → B) *ᵖ (Extend P ρ hρ)) x₀
        ⟨x, pullbackEquiv f ρ hρ x z⟩).2 =
      (trivializationAt H (Extend ((f : B' → B) *ᵖ P) ρ hρ) x₀ ⟨x, z⟩).2
    rw [Pullback.trivializationAt_snd, trivializationAt_pullbackEquiv_snd f ρ hρ hx z]; rfl
  contMDiff_invFun := by
    change ContMDiff (IB'.prod IH) (IB'.prod IH) n
      (ManifoldTotalSpace.fiberwiseMap fun x ↦ (pullbackEquiv f ρ hρ x).symm)
    intro y₀
    have hf_eq : ManifoldTotalSpace.fiberwiseMap (fun x ↦ (pullbackEquiv f ρ hρ x).symm) =
        fun y : ManifoldTotalSpace H ((f : B' → B) *ᵖ (Extend P ρ hρ)) ↦
          ManifoldTotalSpace.homeomorph H _
            ⟨((ManifoldTotalSpace.homeomorph H _).symm y).proj,
              (pullbackEquiv f ρ hρ _).symm ((ManifoldTotalSpace.homeomorph H _).symm y).2⟩ := by
      funext y
      obtain ⟨z, rfl⟩ := (ManifoldTotalSpace.homeomorph H _).surjective y
      rw [ManifoldTotalSpace.fiberwiseMap_homeomorph, Homeomorph.symm_apply_apply]
    rw [hf_eq, ManifoldTotalSpace.contMDiffAt_iff]
    let x₀ := ((ManifoldTotalSpace.homeomorph H _).symm y₀).proj
    have hx₀ : f x₀ ∈ (trivializationAt G P (f x₀)).baseSet := mem_baseSet_trivializationAt G P _
    have hπ := ManifoldTotalSpace.contMDiff_proj n H ((f : B' → B) *ᵖ (Extend P ρ hρ)) IB' IH y₀
    have hv := ManifoldTotalSpace.contMDiffAt_trivializationAt_snd n IB' IH y₀
    refine ⟨hπ, hv.congr_of_eventuallyEq ?_⟩
    filter_upwards [((map_continuous f).continuousAt.comp hπ.continuousAt).preimage_mem_nhds
      ((trivializationAt G P (f x₀)).open_baseSet.mem_nhds hx₀)] with y hy
    obtain ⟨⟨x, w⟩, rfl⟩ := (ManifoldTotalSpace.homeomorph H _).surjective y
    have hx : f x ∈ (trivializationAt G P (f x₀)).baseSet := by simpa using hy
    change (trivializationAt H (Extend ((f : B' → B) *ᵖ P) ρ hρ) x₀
        ⟨((ManifoldTotalSpace.homeomorph H _).symm
            (ManifoldTotalSpace.homeomorph H _ ⟨x, w⟩)).proj,
          (pullbackEquiv f ρ hρ _).symm ((ManifoldTotalSpace.homeomorph H _).symm
            (ManifoldTotalSpace.homeomorph H _ ⟨x, w⟩)).2⟩).2 =
      (trivializationAt H ((f : B' → B) *ᵖ (Extend P ρ hρ)) x₀
        ((ManifoldTotalSpace.homeomorph H _).symm
          (ManifoldTotalSpace.homeomorph H _ ⟨x, w⟩))).2
    rw [Homeomorph.symm_apply_apply]
    change (trivializationAt H (Extend ((f : B' → B) *ᵖ P) ρ hρ) x₀
        ⟨x, (pullbackEquiv f ρ hρ x).symm w⟩).2 =
      (trivializationAt H ((f : B' → B) *ᵖ (Extend P ρ hρ)) x₀ ⟨x, w⟩).2
    rw [Pullback.trivializationAt_snd,
      trivializationAt_pullbackEquiv_snd f ρ hρ hx ((pullbackEquiv f ρ hρ x).symm w),
      Equiv.apply_symm_apply]
    rfl

@[simp]
theorem pullbackDiffeomorph_apply (z : TotalSpace H (Extend ((f : B' → B) *ᵖ P) ρ hρ)) :
    pullbackDiffeomorph (n := n) (IB' := IB') (IH := IH) (P := P) f ρ hρ
        (ManifoldTotalSpace.homeomorph H _ z) =
      ManifoldTotalSpace.homeomorph H _ (pullbackHomeomorph f ρ hρ z) := by
  rw [pullbackHomeomorph_apply]
  exact ManifoldTotalSpace.fiberwiseMap_homeomorph _ z

@[simp]
theorem pullbackDiffeomorph_symm_apply
    (z : TotalSpace H ((f : B' → B) *ᵖ (Extend P ρ hρ))) :
    (pullbackDiffeomorph (n := n) (IB' := IB') (IH := IH) (P := P) f ρ hρ).symm
        (ManifoldTotalSpace.homeomorph H _ z) =
      ManifoldTotalSpace.homeomorph H _ ((pullbackHomeomorph f ρ hρ).symm z) := by
  rw [pullbackHomeomorph_symm_apply]
  exact ManifoldTotalSpace.fiberwiseMap_homeomorph _ z

@[simp]
theorem pullbackDiffeomorph_mk (x : B') (p : P (f x)) (h : H) :
    pullbackDiffeomorph (n := n) (IB' := IB') (IH := IH) (P := P) f ρ hρ
        (ManifoldTotalSpace.homeomorph H _ ⟨x, mk (P := (f : B' → B) *ᵖ P) ρ hρ p h⟩) =
      ManifoldTotalSpace.homeomorph H _ ⟨x, mk (P := P) ρ hρ p h⟩ := by
  rw [pullbackDiffeomorph_apply, pullbackHomeomorph_mk]

end Pullback

/-! ### Nonabelian Čech `H¹` compatibility -/

section CechH1

variable {n : ℕ∞ω} {𝕜 ι B G H : Type*} [NontriviallyNormedField 𝕜]
  {EB : Type*} [NormedAddCommGroup EB] [NormedSpace 𝕜 EB] {HB : Type*} [TopologicalSpace HB]
  {IB : ModelWithCorners 𝕜 EB HB} [TopologicalSpace B] [ChartedSpace HB B]
  {EG : Type*} [NormedAddCommGroup EG] [NormedSpace 𝕜 EG] {HG : Type*} [TopologicalSpace HG]
  {IG : ModelWithCorners 𝕜 EG HG} [Group G] [TopologicalSpace G] [ChartedSpace HG G]
  [LieGroup IG n G]
  {EH : Type*} [NormedAddCommGroup EH] [NormedSpace 𝕜 EH] {HH : Type*} [TopologicalSpace HH]
  {IH : ModelWithCorners 𝕜 EH HH} [Group H] [TopologicalSpace H] [ChartedSpace HH H]
  [ContinuousMul H] [LieGroup IH n H]
  {P : B → Type*} [TopologicalSpace (TotalSpace G P)] [∀ b, TopologicalSpace (P b)]
  [FiberBundle G P] [∀ b, MulAction Gᵐᵒᵖ (P b)] [PrincipalBundle G P]
  [ContMDiffFiberBundle n G P IB IG]

/-- **Extension of structure group acts as `NonabelianCechH1.map` on transition cocycles.** For any
family of base points `u : ι → B` with base sets `U i = (trivializationAt G P (u i)).baseSet`, the
transition cocycle class of `Extend P ρ hρ` in `NonabelianCechH1 IB IH n H U` is the pushforward
along `ρ` of the transition cocycle class of `P`. -/
theorem mk_coordChange_eq_map (u : ι → B) {U : ι → Set B}
    (hu : ∀ i, (trivializationAt G P (u i)).baseSet = U i)
    (ρ : G →* H) (hρ : Continuous ρ) (hρ' : ContMDiff IG IH n ρ)
    [ContMDiffFiberBundle n H (Extend P ρ hρ) IB IH] :
    NonabelianCechH1.mk
        (fun i j x ↦ (trivializationAt H (Extend P ρ hρ) (u i)).coordChange
          (trivializationAt H (Extend P ρ hρ) (u j)) x 1)
        (isContMDiffGroupCocycle_coordChange IB IH n
          (fun i ↦ trivializationAt H (Extend P ρ hρ) (u i))
          (fun i ↦ (baseSet_trivializationAt ρ hρ (u i)).trans (hu i))) =
      NonabelianCechH1.map ρ hρ'
        (NonabelianCechH1.mk
          (fun i j x ↦ (trivializationAt G P (u i)).coordChange (trivializationAt G P (u j)) x 1)
          (isContMDiffGroupCocycle_coordChange IB IG n
            (fun i ↦ trivializationAt G P (u i)) hu)) := by
  rw [NonabelianCechH1.map_mk]
  refine NonabelianCechH1.mk_eq_mk_iff.2 (IsContMDiffCohomologous.of_eqOn fun i j x hx ↦ ?_)
  have hx₁ : x ∈ (trivializationAt G P (u i)).baseSet := (hu i).symm ▸ hx.1
  have hx₂ : x ∈ (trivializationAt G P (u j)).baseSet := (hu j).symm ▸ hx.2
  rw [coordChange_trivializationAt ρ hρ hx₁ hx₂ 1, mul_one]

end CechH1

/-! ### Commutative Lie groups: smooth dual and integer-power bundles -/

section CommGroup

variable (A : Type*) {n : ℕ∞ω} {𝕜 ι B : Type*} [NontriviallyNormedField 𝕜]
  {EB : Type*} [NormedAddCommGroup EB] [NormedSpace 𝕜 EB] {HB : Type*} [TopologicalSpace HB]
  {IB : ModelWithCorners 𝕜 EB HB} [TopologicalSpace B] [ChartedSpace HB B]
  {EA : Type*} [NormedAddCommGroup EA] [NormedSpace 𝕜 EA] {HA : Type*} [TopologicalSpace HA]
  {IA : ModelWithCorners 𝕜 EA HA} [CommGroup A] [TopologicalSpace A] [IsTopologicalGroup A]
  [ChartedSpace HA A]
  (Q : B → Type*) [TopologicalSpace (TotalSpace A Q)] [∀ b, TopologicalSpace (Q b)]
  [FiberBundle A Q] [∀ b, MulAction Aᵐᵒᵖ (Q b)] [PrincipalBundle A Q]

/-- The dual bundle `Dual A Q` of a `C^n` principal `A`-bundle is a `C^n` fibre bundle. -/
instance instContMDiffFiberBundleDual [LieGroup IA n A] [ContMDiffFiberBundle n A Q IB IA] :
    ContMDiffFiberBundle n A (Dual A Q) IB IA :=
  contMDiffFiberBundle IA (contMDiff_inv IA n)

/-- The `k`-th power bundle `ZPow A Q k` of a `C^n` principal `A`-bundle is a `C^n` fibre
bundle. -/
instance instContMDiffFiberBundleZPow [LieGroup IA n A] [ContMDiffFiberBundle n A Q IB IA] (k : ℤ) :
    ContMDiffFiberBundle n A (ZPow A Q k) IB IA :=
  contMDiffFiberBundle IA (contMDiff_zpow k)

/-- **Čech `H¹` class of the dual bundle.** In `NonabelianCechH1 IB IA n A U`, the transition
cocycle class of `Dual A Q` is the inverse of the transition cocycle class of `Q` (corresponding
additively to `-c₁` for circle bundles). -/
theorem mk_coordChange_dual [LieGroup IA n A] [ContMDiffFiberBundle n A Q IB IA]
    (u : ι → B) {U : ι → Set B} (hu : ∀ i, (trivializationAt A Q (u i)).baseSet = U i) :
    NonabelianCechH1.mk
        (fun i j x ↦ (trivializationAt A (Dual A Q) (u i)).coordChange
          (trivializationAt A (Dual A Q) (u j)) x 1)
        (isContMDiffGroupCocycle_coordChange IB IA n
          (fun i ↦ trivializationAt A (Dual A Q) (u i))
          (fun i ↦ (baseSet_trivializationAt _ _ (u i)).trans (hu i))) =
      (NonabelianCechH1.mk
        (fun i j x ↦ (trivializationAt A Q (u i)).coordChange (trivializationAt A Q (u j)) x 1)
        (isContMDiffGroupCocycle_coordChange IB IA n
          (fun i ↦ trivializationAt A Q (u i)) hu))⁻¹ := by
  rw [mk_coordChange_eq_map u hu (invMonoidHom : A →* A) continuous_inv (contMDiff_inv IA n),
    NonabelianCechH1.map_invMonoidHom]

/-- **Čech `H¹` class of the `k`-th power bundle.** In `NonabelianCechH1 IB IA n A U`, the
transition cocycle class of `ZPow A Q k` is the `k`-th power of the transition cocycle class of `Q`
(for `k = 2`, the square class, corresponding additively to `2 c₁` for circle bundles). -/
theorem mk_coordChange_zpow [LieGroup IA n A] [ContMDiffFiberBundle n A Q IB IA] (k : ℤ)
    (u : ι → B) {U : ι → Set B} (hu : ∀ i, (trivializationAt A Q (u i)).baseSet = U i) :
    NonabelianCechH1.mk
        (fun i j x ↦ (trivializationAt A (ZPow A Q k) (u i)).coordChange
          (trivializationAt A (ZPow A Q k) (u j)) x 1)
        (isContMDiffGroupCocycle_coordChange IB IA n
          (fun i ↦ trivializationAt A (ZPow A Q k) (u i))
          (fun i ↦ (baseSet_trivializationAt _ _ (u i)).trans (hu i))) =
      NonabelianCechH1.mk
        (fun i j x ↦ (trivializationAt A Q (u i)).coordChange (trivializationAt A Q (u j)) x 1)
        (isContMDiffGroupCocycle_coordChange IB IA n
          (fun i ↦ trivializationAt A Q (u i)) hu) ^ k := by
  rw [mk_coordChange_eq_map u hu (zpowGroupHom k : A →* A) (continuous_zpow k) (contMDiff_zpow k),
    NonabelianCechH1.map_zpowGroupHom]

/-- Taking the dual bundle twice recovers `Q` up to canonical `C^n` diffeomorphism over `B`. -/
def dualDualDiffeomorph :
    ManifoldTotalSpace A (Dual A (Dual A Q)) ≃ₘ^n⟮IB.prod IA, IB.prod IA⟯
      ManifoldTotalSpace A Q :=
  (compDiffeomorph (n := n) (IB := IB) (IK := IA) (G := A) (P := Q)
      (invMonoidHom : A →* A) continuous_inv (invMonoidHom : A →* A) continuous_inv).trans <|
    (congrDiffeomorph (n := n) (IB := IB) (IH := IA) (G := A) (P := Q)
      invMonoidHom_comp_invMonoidHom (continuous_inv.comp continuous_inv) continuous_id).trans
      (idDiffeomorph (n := n) (IB := IB) (IG := IA) (G := A) (P := Q))

/-- Extending by the `k`-th power and then the `l`-th power is canonically `C^n` diffeomorphic to
extending by the `(k * l)`-th power. -/
def zpowMulDiffeomorph (k l : ℤ) :
    ManifoldTotalSpace A (ZPow A (ZPow A Q k) l) ≃ₘ^n⟮IB.prod IA, IB.prod IA⟯
      ManifoldTotalSpace A (ZPow A Q (k * l)) :=
  (compDiffeomorph (n := n) (IB := IB) (IK := IA) (G := A) (P := Q)
      (zpowGroupHom k : A →* A) (continuous_zpow k)
      (zpowGroupHom l : A →* A) (continuous_zpow l)).trans <|
    congrDiffeomorph (n := n) (IB := IB) (IH := IA) (G := A) (P := Q)
      (by ext a; simp [zpow_mul]) ((continuous_zpow l).comp (continuous_zpow k))
      (continuous_zpow (k * l))

/-- `ZPow A Q (-1)` is canonically `C^n` diffeomorphic to `Dual A Q`. -/
def zpowNegOneDiffeomorph :
    ManifoldTotalSpace A (ZPow A Q (-1)) ≃ₘ^n⟮IB.prod IA, IB.prod IA⟯
      ManifoldTotalSpace A (Dual A Q) :=
  congrDiffeomorph (n := n) (IB := IB) (IH := IA) (G := A) (P := Q) (by ext a; simp)
    (continuous_zpow (-1)) continuous_inv

/-- Extending `Q` along the diagonal `a ↦ (a, a) : A →* A × A` and then along group multiplication
`mulMonoidHom : A × A →* A` is canonically `C^n` diffeomorphic to the square bundle `ZPow A Q 2`
(`a ↦ a ^ 2`). -/
def diagMulZPowTwoDiffeomorph :
    ManifoldTotalSpace A
        (Extend (Extend Q (MonoidHom.prod (.id A) (.id A)) (continuous_id.prodMk continuous_id))
          (mulMonoidHom : A × A →* A) continuous_mul) ≃ₘ^n⟮IB.prod IA, IB.prod IA⟯
      ManifoldTotalSpace A (ZPow A Q 2) :=
  (compDiffeomorph (n := n) (IB := IB) (IK := IA) (G := A) (P := Q)
      (MonoidHom.prod (.id A) (.id A)) (continuous_id.prodMk continuous_id)
      (mulMonoidHom : A × A →* A) continuous_mul).trans <|
    congrDiffeomorph (n := n) (IB := IB) (IH := IA) (G := A) (P := Q) (by ext a; simp [sq])
      (continuous_mul.comp (continuous_id.prodMk continuous_id)) (continuous_zpow 2)

end CommGroup

end TauCeti.PrincipalBundle.Extend
