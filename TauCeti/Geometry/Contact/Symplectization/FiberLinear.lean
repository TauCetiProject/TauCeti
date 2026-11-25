/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.Geometry.Contact.Symplectization.Annihilator
public import TauCeti.Geometry.Contact.Symplectization.Hamiltonian
public import TauCeti.Geometry.Contact.VectorField.ContactLine
import Mathlib.Geometry.Manifold.PartitionOfUnity
import TauCeti.Geometry.Manifold.SmoothEmbedding.Basic
import TauCeti.Geometry.Manifold.VectorBundle.Bilinear.SmulRight

/-!
# Fibre-linear functions on the symplectization

Let `ξ` be a contact structure on a finite-dimensional manifold `M`, with contact line
`L = TM ⧸ ξ`, and let `ξ⁰ ⊂ T*M` be its annihilator line, the dual `L*` of the contact line. A
vector field `V` on `M` represents the section `[V]` of `L`, and determines the function

`F_V(z) = z(V x)` for a covector `z ∈ ξ⁰` over `x`

(`TauCeti.CotangentBundle.annihilatorPairing`). It is linear on each fibre of `ξ⁰`
(`TauCeti.CotangentBundle.annihilatorPairing_mk_smul`), smooth for smooth `V`
(`TauCeti.CotangentBundle.contMDiff_annihilatorPairing`), and depends exactly on the section
`[V]` of `L`: `F_V = F_W` if and only if `V - W` is tangent to `ξ`
(`TauCeti.CotangentBundle.annihilatorPairing_eq_annihilatorPairing_iff`). These are the functions
`ℓ ↦ ℓ(s)` on `L* ∖ 0` attached to the sections `s` of `L`, and on a σ-compact manifold they are
all the smooth functions on `ξ⁰ ∖ 0` that are linear on the fibres, `F(c ℓ) = c F(ℓ)` for real
`c ≠ 0` (`TauCeti.IsContactDistribution.exists_contMDiff_annihilatorPairing_eq_iff`): near each
point, with a local contact form `α`, the vector field `F(α) R_α` has function `F`, and a partition
of unity glues these local solutions.

The symplectization `ξ⁰ ∖ 0` carries the symplectic form `dθ` of the tautological one-form `θ`
(`TauCeti.IsContactDistribution.annihilatorLiouvilleForm`). With the conventions `ι_(X_F) dθ = dF`
and `{F, G} = dθ(X_F, X_G)`, the Poisson bracket of two fibre-linear functions is again
fibre-linear, and is the function of the bracket of sections of the contact line:

`{F_V, F_W} = F_([X_V, X_W])`

(`TauCeti.IsContactDistribution.poissonBracket_annihilatorPairing`), where `X_V` is the contact
vector field in the class of `V` (`TauCeti.contactVectorField`). The left side is defined by the
symplectic form of `ξ⁰ ∖ 0` alone, so this identifies the bracket of sections of `L` of
`TauCeti.Geometry.Contact.VectorField.ContactLine` with the Poisson bracket of the symplectization,
without choosing a contact form or a coorientation.

The bracket identity is local. At a nonzero covector `z` over `x`, choose a local contact form
`β` of `ξ` near `x`, with sign such that `z = eᵗ β_x`, and a local lift `κ` of `(s, y) ↦ eˢ β_y`
into `ξ⁰` (`TauCeti.IsContactDistribution.exists_lift_symplectizationToCotangent`). The
differential of `κ` at `(t, x)` carries `d(eˢ β)` to `dθ` and is bijective, and `F_V ∘ κ` is
`(s, y) ↦ eˢ β_y(V y)` near `(t, x)`. So `κ` identifies the Hamiltonian vectors and the Poisson
bracket at `z` with those of `eˢ β(V)` and `eˢ β(W)` at `(t, x)`, which is `eᵗ {β(V), β(W)}_β(x)`
(`TauCeti.SmoothForm.poissonBracket_symplectization_exp_mul_of_isContactFormAt`). In the local
contact form `β` the bracket of sections of `L` is the Jacobi bracket,
`β([X_V, X_W]) = {β(V), β(W)}_β` at `x`
(`TauCeti.IsContactDistribution.apply_mlieBracket_contactVectorField`), and `eᵗ β_x = z`.

## Main definitions

* `TauCeti.CotangentBundle.annihilatorPairing`: the fibre-linear function `z ↦ z(V)` on the
  annihilator bundle of a distribution.

## Main results

* `TauCeti.CotangentBundle.annihilatorPairing_eq_annihilatorPairing_iff`: `F_V = F_W` exactly when
  `V - W` lies in the distribution.
* `TauCeti.IsContactDistribution.exists_contMDiff_annihilatorPairing_eq_iff`: the smooth
  fibre-linear functions on `ξ⁰ ∖ 0` are exactly the functions `F_V` of smooth vector fields.
* `TauCeti.IsContactDistribution.poissonBracket_annihilatorPairing`: `{F_V, F_W} = F_([X_V, X_W])`
  at every nonzero covector of `ξ⁰`.
* `TauCeti.IsContactDistribution.poissonBracket_annihilatorPairing_comp_subtypeVal`: the same
  identity for the symplectic form of `ξ⁰ ∖ 0`.

## References

* V. I. Arnold, *Mathematical Methods of Classical Mechanics*, second edition, Springer, 1989,
  Appendix 4 (contact Hamiltonians as homogeneous functions on the symplectization).
* H. Geiges, *An Introduction to Contact Topology*, Cambridge University Press, 2008,
  Section 2.3 (contact Hamiltonians).
-/

public section

noncomputable section

open Bundle Filter Function Manifold Set Topology VectorField
open scoped Manifold ContDiff

namespace TauCeti

namespace CotangentBundle

/-! ### Fibre-linear functions on the annihilator bundle -/

section Pairing

variable {𝕜 : Type*} [NontriviallyNormedField 𝕜]
  {E : Type*} [NormedAddCommGroup E] [NormedSpace 𝕜 E]
  {H : Type*} [TopologicalSpace H] {I : ModelWithCorners 𝕜 E H}
  {M : Type*} [TopologicalSpace M] [ChartedSpace H M]
  {D : Π x : M, Submodule 𝕜 (TangentSpace I x)} {P : Type*}

/-- The **fibre-linear function of a vector field** `V` on the annihilator bundle of a distribution
`D`: a covector `z` annihilating `D` over `x` is sent to `z(V x)`. It is linear on each fibre and
depends only on `V` modulo `D`
(`TauCeti.CotangentBundle.annihilatorPairing_eq_annihilatorPairing_iff`). -/
def annihilatorPairing (V : Π x : M, TangentSpace I x)
    (z : TotalSpace P fun x ↦ annihilatorSpace I D x) : 𝕜 :=
  (z.snd : TangentSpace I z.proj →L[𝕜] 𝕜) (V z.proj)

/-- The fibre-linear function of `V` evaluates the covector on `V` at its base point. -/
@[simp]
theorem annihilatorPairing_apply (V : Π x : M, TangentSpace I x)
    (z : TotalSpace P fun x ↦ annihilatorSpace I D x) :
    annihilatorPairing V z = (z.snd : TangentSpace I z.proj →L[𝕜] 𝕜) (V z.proj) :=
  (rfl)

/-- The fibre-linear function of `V` is the value on `V` of the covector in `T*M`. -/
theorem annihilatorPairing_eq_snd_annihilatorInclusion (V : Π x : M, TangentSpace I x)
    (z : TotalSpace P fun x ↦ annihilatorSpace I D x) :
    annihilatorPairing V z =
      (annihilatorInclusion I D P z).snd (V (annihilatorInclusion I D P z).proj) := by
  rw [annihilatorInclusion_apply]
  rfl

/-- **Fibre-linearity.** The function of `V` is linear on each fibre of the annihilator bundle. -/
theorem annihilatorPairing_mk_smul (V : Π x : M, TangentSpace I x) (x : M) (c : 𝕜)
    (q : annihilatorSpace I D x) :
    annihilatorPairing V (TotalSpace.mk' P x (c • q)) =
      c * annihilatorPairing V (TotalSpace.mk' P x q) := by
  simp

/-- The function of a sum of vector fields is the sum of their functions. -/
theorem annihilatorPairing_add (V W : Π x : M, TangentSpace I x) :
    annihilatorPairing (P := P) (D := D) (V + W) =
      annihilatorPairing V + annihilatorPairing W := by
  ext z
  simp

/-- The function of a constant multiple of a vector field is the multiple of its function. -/
theorem annihilatorPairing_smul (c : 𝕜) (V : Π x : M, TangentSpace I x) :
    annihilatorPairing (P := P) (D := D) (c • V) = c • annihilatorPairing V := by
  ext z
  simp

/-- **Fibre-linear functions are the sections of `TM ⧸ D`.** On a finite-dimensional manifold, two
vector fields have the same function on the annihilator bundle of `D` exactly when their
difference is tangent to `D`. -/
theorem annihilatorPairing_eq_annihilatorPairing_iff [CompleteSpace 𝕜] [FiniteDimensional 𝕜 E]
    {V W : Π x : M, TangentSpace I x} :
    annihilatorPairing (P := P) (D := D) V = annihilatorPairing W ↔ ∀ x, V x - W x ∈ D x := by
  refine ⟨fun h x ↦ mem_iff_forall_mem_annihilatorSpace.2 fun q hq ↦ ?_, fun h ↦ ?_⟩
  · have hx := congrFun h (TotalSpace.mk' P x ⟨q, hq⟩)
    simp only [annihilatorPairing_apply] at hx
    rw [map_sub, hx, sub_self]
  · ext z
    rw [annihilatorPairing_apply, annihilatorPairing_apply, ← sub_eq_zero, ← map_sub]
    exact mem_annihilatorSpace_iff.1 z.snd.property _ (h z.proj)

end Pairing

section Symplectization

variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
  {H : Type*} [TopologicalSpace H] {I : ModelWithCorners ℝ E H}
  {M : Type*} [TopologicalSpace M] [ChartedSpace H M] [IsManifold I ∞ M]
  {D : Π x : M, Submodule ℝ (TangentSpace I x)} {P : Type*}

/-- **Fibre-linear functions in a trivialization of the symplectization.** If a map
`κ : ℝ × M → D⁰`, composed with the inclusion `D⁰ → T*M`, agrees near `p` with
`(s, y) ↦ eˢ β_y` for a one-form `β`, then near `p` the function of `V` reads
`F_V ∘ κ = (s, y) ↦ eˢ β_y(V y)`. -/
theorem annihilatorPairing_comp_eventuallyEq {V : Π x : M, TangentSpace I x}
    {κ : ℝ × M → TotalSpace P fun x ↦ annihilatorSpace I D x} {β : SmoothForm I M ℝ 1}
    {p : ℝ × M} (hev : annihilatorInclusion I D P ∘ κ =ᶠ[𝓝 p] β.symplectizationToCotangent) :
    annihilatorPairing V ∘ κ =ᶠ[𝓝 p] fun q ↦ Real.exp q.1 * β.val q.2 ![V q.2] := by
  filter_upwards [hev] with q hq
  rw [comp_apply, annihilatorPairing_eq_snd_annihilatorInclusion]
  calc _ = (β.symplectizationToCotangent q).snd (V (β.symplectizationToCotangent q).proj) :=
        congrArg (fun w : CotangentBundle I M ↦ w.snd (V w.proj)) hq
    _ = Real.exp q.1 * β.val q.2 ![V (β.symplectizationToCotangent q).proj] :=
        SmoothForm.symplectizationToCotangent_snd_apply β q _
    _ = Real.exp q.1 * β.val q.2 ![V q.2] := by
        rw [SmoothForm.proj_symplectizationToCotangent]

end Symplectization

section Smooth

variable {𝕜 : Type*} [NontriviallyNormedField 𝕜] [IsRCLikeNormedField 𝕜]
  {E : Type*} [NormedAddCommGroup E] [NormedSpace 𝕜 E] [FiniteDimensional 𝕜 E]
  {H : Type*} [TopologicalSpace H] {I : ModelWithCorners 𝕜 E H}
  {M : Type*} [TopologicalSpace M] [ChartedSpace H M]
  {D : Π x : M, Submodule 𝕜 (TangentSpace I x)} {n : ℕ∞ω} {k r : ℕ}
  [IsManifold I 1 M] [IsManifold I (n + 1) M]

/-- **Smoothness of fibre-linear functions.** For a `C^n` distribution `D` of rank `k` on a
manifold of dimension `k + r`, the function of a `C^n` vector field `V` on the annihilator bundle
of `D` is `C^n`. -/
theorem contMDiff_annihilatorPairing (hD : IsContMDiffDistribution I n k D)
    (hk : k + r = Module.finrank 𝕜 E) {V : Π x : M, TangentSpace I x}
    (hV : ContMDiff I I.tangent n (T% V)) :
    letI := hD.annihilatorFiberBundle hk
    ContMDiff (I.prod 𝓘(𝕜, Fin r → 𝕜)) 𝓘(𝕜) n
      (annihilatorPairing (P := Fin r → 𝕜) (D := D) V) :=
  letI := hD.annihilatorFiberBundle hk
  by
  have hj := hD.contMDiff_annihilatorInclusion hk
  -- The inclusion into `T*M` is the covector field `z ↦ z` along the bundle projection.
  rw [show annihilatorInclusion I D (Fin r → 𝕜) = fun z ↦ ⟨z.proj, z.snd⟩ from
    funext (annihilatorInclusion_apply I D _)] at hj
  exact fun z ↦ ContMDiffAt.clm_bundle_apply_scalar (V := TangentSpace I)
    (b := fun w : TotalSpace (Fin r → 𝕜) (fun x ↦ annihilatorSpace I D x) ↦ w.proj)
    (hj z) ((hV.comp (Bundle.contMDiff_proj fun x ↦ annihilatorSpace I D x)) z)

end Smooth

end CotangentBundle

namespace IsContactDistribution

open CotangentBundle

variable {E H M : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E] [FiniteDimensional ℝ E]
  [TopologicalSpace H] {I : ModelWithCorners ℝ E H} [TopologicalSpace M] [ChartedSpace H M]
  [IsManifold I ∞ M] {ξ : Π x : M, Submodule ℝ (TangentSpace I x)}
  {V W : Π x : M, TangentSpace I x}

/-- `C^(∞ + 1)` charts, needed by the annihilator bundle construction of
`TauCeti.IsContMDiffDistribution.annihilatorContMDiffVectorBundle` at smoothness `∞`. -/
local instance : IsManifold I ((∞ : WithTop ℕ∞) + 1) M := IsManifold.of_le (n := ∞) (by simp)

variable [Nonempty M] [T2Space M] (hξ : IsContactDistribution I ∞ ξ)

/-! ### Fibre-linear functions are the sections of the contact line -/

/-- Near every point of a contact manifold, a function `F` on `ξ⁰` that is smooth at the nonzero
covectors and linear on the fibres is, at the nonzero covectors, the fibre-linear function of a
vector field defined and smooth near that point: with a local contact form `α`, the field
`F(α) R_α`. -/
private theorem exists_local_annihilatorPairing_eq
    {F : TotalSpace (Fin 1 → ℝ) (fun x ↦ annihilatorSpace I ξ x) → ℝ} :
    letI := hξ.isContMDiffDistribution.annihilatorFiberBundle hξ.finrank_sub_one_add_one
    (∀ z : TotalSpace (Fin 1 → ℝ) (fun x ↦ annihilatorSpace I ξ x), z.snd ≠ 0 →
        ContMDiffAt (I.prod 𝓘(ℝ, Fin 1 → ℝ)) 𝓘(ℝ) ∞ F z) →
      (∀ (x : M) (c : ℝ) (q : annihilatorSpace I ξ x), c ≠ 0 → q ≠ 0 →
        F (TotalSpace.mk' (Fin 1 → ℝ) x (c • q)) = c * F (TotalSpace.mk' (Fin 1 → ℝ) x q)) →
      ∀ x₀ : M, ∃ U ∈ 𝓝 x₀, ∃ s : Π x : M, TangentSpace I x, CMDiff[U] ∞ (T% s) ∧
        ∀ y ∈ U, ∀ q : annihilatorSpace I ξ y, q ≠ 0 →
          (q : TangentSpace I y →L[ℝ] ℝ) (s y) = F (TotalSpace.mk' (Fin 1 → ℝ) y q) :=
  letI := hξ.isContMDiffDistribution.annihilatorFiberBundle hξ.finrank_sub_one_add_one
  haveI := hξ.isContMDiffDistribution.annihilatorVectorBundle hξ.finrank_sub_one_add_one
  fun hF hhom x₀ ↦ by
  classical
  obtain ⟨W, hW, hx₀, α, hα⟩ := hξ.exists_smoothForm_ker_eq_isContactFormAt x₀
  have hker (y : M) (hy : y ∈ W) :
      LinearMap.ker (SmoothForm.degreeOneEquiv α y).toLinearMap = ξ y := by
    rw [← (hα y hy).1]
    ext v
    simp [RoughForm.mem_ker, SmoothForm.degreeOneEquiv_apply_apply_vec]
  have hmem (y : M) (hy : y ∈ W) : SmoothForm.degreeOneEquiv α y ∈ annihilatorSpace I ξ y := by
    rw [annihilatorSpace_eq_span_singleton (hker y hy)]
    exact Submodule.mem_span_singleton_self _
  -- The section `y ↦ α_y` of `ξ⁰` over `W`, extended by zero.
  let ℓ : M → TotalSpace (Fin 1 → ℝ) (fun x ↦ annihilatorSpace I ξ x) := fun y ↦
    if hy : y ∈ W then TotalSpace.mk' (Fin 1 → ℝ) y ⟨_, hmem y hy⟩
    else zeroSection (Fin 1 → ℝ) _ y
  have hℓ (y : M) (hy : y ∈ W) : ℓ y = TotalSpace.mk' (Fin 1 → ℝ) y ⟨_, hmem y hy⟩ := by
    simp [ℓ, hy]
  have hℓne (y : M) (hy : y ∈ W) : (ℓ y).snd ≠ 0 := by
    rw [hℓ y hy]
    intro h
    -- `α_y` vanishes on every vector, so `α y = 0`, contradicting the contact condition.
    refine (hα y hy).2.ne_zero (ContinuousAlternatingMap.ext fun v ↦ ?_)
    have hv := DFunLike.congr_fun (congrArg Subtype.val h) (v 0)
    rwa [SmoothForm.degreeOneEquiv_apply_apply_vec,
      show ![v 0] = v from funext fun i ↦ by rw [Subsingleton.elim i 0]; rfl] at hv
  have hℓs (y : M) (hy : y ∈ W) : ContMDiffAt I (I.prod 𝓘(ℝ, Fin 1 → ℝ)) ∞ ℓ y := by
    rw [(hξ.isContMDiffDistribution.isSmoothEmbedding_annihilatorInclusion (n := ∞)
      hξ.finrank_sub_one_add_one).contMDiffAt_iff_comp]
    refine ((SmoothForm.degreeOneEquiv α).contMDiff y).congr_of_eventuallyEq ?_
    filter_upwards [hW.mem_nhds hy] with y' hy'
    rw [comp_apply, hℓ y' hy', annihilatorInclusion_mk']
  have hRW : ∀ y ∈ W, ∀ᶠ y' in 𝓝 y, IsContactFormAt α.val y' := fun y hy ↦
    Filter.eventually_of_mem (hW.mem_nhds hy) fun y' hy' ↦ (hα y' hy').2
  refine ⟨W, hW.mem_nhds hx₀, fun y ↦ F (ℓ y) • α.reebVectorField y,
    fun y hy ↦ (((hF _ (hℓne y hy)).comp y (hℓs y hy)).smul_section
      (SmoothForm.contMDiffAt_reebVectorField (hRW y hy))).contMDiffWithinAt, fun y hy q hq ↦ ?_⟩
  -- A nonzero `q ∈ ξ⁰_y` is `c α_y` with `c ≠ 0`, and `α_y(R_α) = 1`.
  have hqα : (q : TangentSpace I y →L[ℝ] ℝ) ∈ ℝ ∙ SmoothForm.degreeOneEquiv α y := by
    rw [← annihilatorSpace_eq_span_singleton (hker y hy)]
    exact q.property
  obtain ⟨c, hc⟩ := Submodule.mem_span_singleton.1 hqα
  have hq' : q = c • ⟨_, hmem y hy⟩ := Subtype.ext (by rw [Submodule.coe_smul]; exact hc.symm)
  have hc0 : c ≠ 0 := by
    rintro rfl
    exact hq (by rw [hq', zero_smul])
  rw [hq', hhom y c _ hc0 (fun h ↦ hℓne y hy (by rw [hℓ y hy]; exact h)), ← hℓ y hy,
    Submodule.coe_smul, smul_apply, map_smul,
    SmoothForm.degreeOneEquiv_apply_apply_vec, SmoothForm.apply_reebVectorField_of_isContactFormAt
      (hα y hy).2, smul_eq_mul, smul_eq_mul, mul_one, mul_comm]

/-- **The smooth fibre-linear functions on the symplectization.** On a σ-compact contact manifold
`(M, ξ)`, a function `F` on `ξ⁰` agrees at every nonzero covector with the fibre-linear function
`F_V(z) = z(V)` of a smooth vector field `V` if and only if it is smooth at the nonzero covectors
and linear on the fibres, `F(c q) = c F(q)` for every real `c ≠ 0` and nonzero `q ∈ ξ⁰_x`. So the
smooth functions on `ξ⁰ ∖ 0` that are linear on the fibres are exactly the functions `ℓ ↦ ℓ(s)` of
the smooth sections `s = [V]` of the contact line, and by
`TauCeti.CotangentBundle.annihilatorPairing_eq_annihilatorPairing_iff` the section is unique. No
contact form or coorientation of `ξ` is used. -/
theorem exists_contMDiff_annihilatorPairing_eq_iff [SigmaCompactSpace M]
    {F : TotalSpace (Fin 1 → ℝ) (fun x ↦ annihilatorSpace I ξ x) → ℝ} :
    letI := hξ.isContMDiffDistribution.annihilatorFiberBundle hξ.finrank_sub_one_add_one
    (∃ V : Π x : M, TangentSpace I x, CMDiff ∞ (T% V) ∧
        ∀ z : TotalSpace (Fin 1 → ℝ) (fun x ↦ annihilatorSpace I ξ x), z.snd ≠ 0 →
          F z = annihilatorPairing V z) ↔
      (∀ z : TotalSpace (Fin 1 → ℝ) (fun x ↦ annihilatorSpace I ξ x), z.snd ≠ 0 →
          ContMDiffAt (I.prod 𝓘(ℝ, Fin 1 → ℝ)) 𝓘(ℝ) ∞ F z) ∧
        ∀ (x : M) (c : ℝ) (q : annihilatorSpace I ξ x), c ≠ 0 → q ≠ 0 →
          F (TotalSpace.mk' (Fin 1 → ℝ) x (c • q)) = c * F (TotalSpace.mk' (Fin 1 → ℝ) x q) :=
  letI := hξ.isContMDiffDistribution.annihilatorFiberBundle hξ.finrank_sub_one_add_one
  haveI := hξ.isContMDiffDistribution.annihilatorVectorBundle hξ.finrank_sub_one_add_one
  by
  refine ⟨fun ⟨V, hV, hFV⟩ ↦ ⟨fun z hz ↦ ?_, fun x c q hc hq ↦ ?_⟩, fun ⟨hF, hhom⟩ ↦ ?_⟩
  · -- `F` agrees with the smooth function `F_V` on the open set of nonzero covectors.
    refine (contMDiff_annihilatorPairing hξ.isContMDiffDistribution hξ.finrank_sub_one_add_one hV
      z).congr_of_eventuallyEq ?_
    filter_upwards [(isOpen_zeroSectionCompl (Fin 1 → ℝ) _).mem_nhds
      (mem_zeroSectionCompl.2 hz)] with w hw
    exact hFV w (mem_zeroSectionCompl.1 hw)
  · rw [hFV _ (smul_ne_zero hc hq), hFV _ hq, annihilatorPairing_mk_smul]
  -- The admissible values of `V` at `x`: vectors on which every nonzero `q ∈ ξ⁰_x` takes the
  -- value `F(q)`. They form an affine subspace, hence a convex set.
  set t : ∀ x : M, Set (TangentSpace I x) := fun x ↦
    {v | ∀ q : annihilatorSpace I ξ x, q ≠ 0 →
      (q : TangentSpace I x →L[ℝ] ℝ) v = F (TotalSpace.mk' (Fin 1 → ℝ) x q)}
  have ht (x : M) : Convex ℝ (t x) := fun u hu v hv a b _ _ hab q hq ↦ by
    rw [map_add, map_smul, map_smul, hu q hq, hv q hq, smul_eq_mul, smul_eq_mul, ← add_mul, hab,
      one_mul]
  obtain ⟨s, hs⟩ := exists_contMDiffSection_forall_mem_convex_of_local I (TangentSpace I) t ht
    (exists_local_annihilatorPairing_eq hξ hF hhom)
  exact ⟨s, s.contMDiff, fun z hz ↦ (hs z.proj z.snd hz).symm⟩

/-! ### The Poisson bracket of fibre-linear functions -/

/-- In a local trivialization `κ` of the symplectization through a nonzero covector `z = κ(t, x)`,
built from a one-form `β` that is a contact form at `x`, the differential of `κ` carries the
Hamiltonian vector of `(s, y) ↦ eˢ β_y(U y)` for `d(eˢ β)` at `(t, x)` to the Hamiltonian vector of
the fibre-linear function `F_U` for `dθ` at `z`. -/
private theorem hamiltonianVectorField_annihilatorPairing_of_lift
    {U : Π x : M, TangentSpace I x} (hU : CMDiff ∞ (T% U))
    {z : TotalSpace (Fin 1 → ℝ) fun x ↦ annihilatorSpace I ξ x} (hz : z.snd ≠ 0)
    {β : SmoothForm I M ℝ 1} (hβ : IsContactFormAt β.val z.proj) {t : ℝ}
    {κ : ℝ × M → TotalSpace (Fin 1 → ℝ) fun x ↦ annihilatorSpace I ξ x}
    (hκp : κ (t, z.proj) = z)
    (hev : annihilatorInclusion I ξ (Fin 1 → ℝ) ∘ κ =ᶠ[𝓝 (t, z.proj)]
      β.symplectizationToCotangent) :
    letI := hξ.isContMDiffDistribution.annihilatorFiberBundle hξ.finrank_sub_one_add_one
    haveI := hξ.isContMDiffDistribution.annihilatorVectorBundle hξ.finrank_sub_one_add_one
    haveI := hξ.isContMDiffDistribution.annihilatorContMDiffVectorBundle
      hξ.finrank_sub_one_add_one
    ContMDiffAt (𝓘(ℝ).prod I) (I.prod 𝓘(ℝ, Fin 1 → ℝ)) ∞ κ (t, z.proj) →
      SmoothTwoForm.hamiltonianVectorField
          (mextDerivₗ (I.prod 𝓘(ℝ, Fin 1 → ℝ)) 1 hξ.annihilatorLiouvilleForm)
          (annihilatorPairing U) (κ (t, z.proj)) =
        mfderiv (𝓘(ℝ).prod I) (I.prod 𝓘(ℝ, Fin 1 → ℝ)) κ (t, z.proj)
          (SmoothTwoForm.hamiltonianVectorField (mextDerivₗ (𝓘(ℝ).prod I) 1 β.symplectization)
            (fun q ↦ Real.exp q.1 * β.val q.2 ![U q.2]) (t, z.proj)) :=
  letI := hξ.isContMDiffDistribution.annihilatorFiberBundle hξ.finrank_sub_one_add_one
  haveI := hξ.isContMDiffDistribution.annihilatorVectorBundle hξ.finrank_sub_one_add_one
  haveI := hξ.isContMDiffDistribution.annihilatorContMDiffVectorBundle hξ.finrank_sub_one_add_one
  fun hκ ↦ by
  have hκd := hκ.mdifferentiableAt (n := ∞) (by simp)
  set D := mfderiv (𝓘(ℝ).prod I) (I.prod 𝓘(ℝ, Fin 1 → ℝ)) κ (t, z.proj)
  have hD := hξ.eval₂_mextDerivₗ_annihilatorLiouvilleForm_mfderiv hev hκd
  have hσinv : (SmoothTwoForm.flat (mextDerivₗ (𝓘(ℝ).prod I) 1 β.symplectization)
      (t, z.proj)).IsInvertible := SmoothTwoForm.isInvertible_flat_iff.2
    ((SmoothForm.nondegenerate_bilinFormAt_mextDerivₗ_symplectization_iff β (t, z.proj)).2 hβ)
  have hωinv : (SmoothTwoForm.flat (mextDerivₗ (I.prod 𝓘(ℝ, Fin 1 → ℝ)) 1
      hξ.annihilatorLiouvilleForm) (κ (t, z.proj))).IsInvertible := by
    rw [SmoothTwoForm.isInvertible_flat_iff, hκp]
    exact hξ.nondegenerate_bilinFormAt_mextDerivₗ_annihilatorLiouvilleForm hz
  -- `D = dκ` carries `d(eˢ β)` to `dθ`, so it is injective, hence bijective by dimension.
  have hinj : Injective D := (injective_iff_map_eq_zero D).2 fun u hu ↦
    (injective_iff_map_eq_zero _).1 hσinv.injective u <| ContinuousLinearMap.ext fun u' ↦ by
      rw [SmoothTwoForm.flat_apply, ← hD, hu, SmoothBundleForm.eval₂_zero_left, zero_apply]
  have hfin : Module.finrank ℝ (ℝ × E) = Module.finrank ℝ (E × (Fin 1 → ℝ)) := by
    simp only [Module.finrank_prod, Module.finrank_self, Module.finrank_fin_fun, add_comm]
  have hDsurj : Surjective D :=
    (LinearMap.injective_iff_surjective_of_finrank_eq_finrank hfin (f := D.toLinearMap)).1 hinj
  have hF : MDifferentiableAt (I.prod 𝓘(ℝ, Fin 1 → ℝ)) 𝓘(ℝ) (annihilatorPairing U)
      (κ (t, z.proj)) :=
    (contMDiff_annihilatorPairing hξ.isContMDiffDistribution hξ.finrank_sub_one_add_one hU
      _).mdifferentiableAt (by simp)
  -- Test the Hamiltonian equation of `F_U` at `z` on the vectors `D u`.
  rw [SmoothTwoForm.hamiltonianVectorField_eq_iff_of_isInvertible_flat hωinv]
  intro w
  obtain ⟨u, rfl⟩ := hDsurj w
  rw [hD, SmoothTwoForm.eval₂_hamiltonianVectorField_of_isInvertible hσinv,
    ← (annihilatorPairing_comp_eventuallyEq hev).mvfderiv_eq, mvfderiv_comp_apply _ hF hκd]

/-- **The Poisson bracket of fibre-linear functions on the symplectization.** For smooth vector
fields `V` and `W` on a contact manifold `(M, ξ)`, the Poisson bracket for `dθ` of the
fibre-linear functions `F_V(z) = z(V)` and `F_W(z) = z(W)` at a nonzero covector `z` of `ξ⁰` is
`F_([X_V, X_W])(z)`, where `X_V` and `X_W` are the contact vector fields in the classes of `V` and
`W` modulo `ξ`: `{F_V, F_W} = F_([X_V, X_W])`. No contact form or coorientation of `ξ` is used. -/
theorem poissonBracket_annihilatorPairing (hV : CMDiff ∞ (T% V)) (hW : CMDiff ∞ (T% W))
    {z : TotalSpace (Fin 1 → ℝ) fun x ↦ annihilatorSpace I ξ x} (hz : z.snd ≠ 0) :
    letI := hξ.isContMDiffDistribution.annihilatorFiberBundle hξ.finrank_sub_one_add_one
    haveI := hξ.isContMDiffDistribution.annihilatorVectorBundle hξ.finrank_sub_one_add_one
    haveI := hξ.isContMDiffDistribution.annihilatorContMDiffVectorBundle
      hξ.finrank_sub_one_add_one
    SmoothTwoForm.poissonBracket
        (mextDerivₗ (I.prod 𝓘(ℝ, Fin 1 → ℝ)) 1 hξ.annihilatorLiouvilleForm)
        (annihilatorPairing V) (annihilatorPairing W) z =
      annihilatorPairing (mlieBracket I (contactVectorField I ξ V) (contactVectorField I ξ W)) z :=
  letI := hξ.isContMDiffDistribution.annihilatorFiberBundle hξ.finrank_sub_one_add_one
  haveI := hξ.isContMDiffDistribution.annihilatorVectorBundle hξ.finrank_sub_one_add_one
  haveI := hξ.isContMDiffDistribution.annihilatorContMDiffVectorBundle hξ.finrank_sub_one_add_one
  by
  -- A local contact form `β` with `z = eᵗ β_x`, and a local lift `κ` of `(s, y) ↦ eˢ β_y`.
  obtain ⟨β, t, κ, hβξ, hβ, hκp, hev, hκ⟩ := hξ.exists_lift_symplectizationToCotangent hz
  have hf (U : Π x : M, TangentSpace I x) (hU : CMDiff ∞ (T% U)) :
      MDifferentiableAt I 𝓘(ℝ) (fun y ↦ β.val y ![U y]) (t, z.proj).2 :=
    (β.contMDiff_apply_vectorField hU _).mdifferentiableAt (by simp)
  -- The value of `F_([X_V, X_W])` at `z = κ (t, x)` is `eᵗ β_x([X_V, X_W])`.
  have hR := (annihilatorPairing_comp_eventuallyEq
    (V := mlieBracket I (contactVectorField I ξ V) (contactVectorField I ξ W)) hev).self_of_nhds
  rw [comp_apply] at hR
  -- Through `dκ`, the bracket at `z` is `{eˢ β(V), eˢ β(W)} = eᵗ {β(V), β(W)}_β` at `(t, x)`.
  rw [← hκp, SmoothTwoForm.poissonBracket_def,
    hamiltonianVectorField_annihilatorPairing_of_lift hξ hV hz hβ hκp hev hκ,
    hamiltonianVectorField_annihilatorPairing_of_lift hξ hW hz hβ hκp hev hκ,
    hξ.eval₂_mextDerivₗ_annihilatorLiouvilleForm_mfderiv hev (hκ.mdifferentiableAt (by simp)),
    ← SmoothTwoForm.poissonBracket_def,
    SmoothForm.poissonBracket_symplectization_exp_mul_of_isContactFormAt hβ (hf V hV) (hf W hW),
    hR]
  dsimp only
  rw [hξ.apply_mlieBracket_contactVectorField hV hW hβξ, SmoothForm.jacobiBracket_def]

/-- **The Poisson bracket of fibre-linear functions on `ξ⁰ ∖ 0`.** For the symplectic form `dθ` of
the symplectization `ξ⁰ ∖ 0`, the Poisson bracket of the restrictions of the fibre-linear
functions `F_V` and `F_W` is the restriction of `F_([X_V, X_W])`. -/
theorem poissonBracket_annihilatorPairing_comp_subtypeVal (hV : CMDiff ∞ (T% V))
    (hW : CMDiff ∞ (T% W)) :
    letI := hξ.isContMDiffDistribution.annihilatorFiberBundle hξ.finrank_sub_one_add_one
    haveI := hξ.isContMDiffDistribution.annihilatorVectorBundle hξ.finrank_sub_one_add_one
    haveI := hξ.isContMDiffDistribution.annihilatorContMDiffVectorBundle
      hξ.finrank_sub_one_add_one
    ∀ z : hξ.annihilatorPunctured,
      SmoothTwoForm.poissonBracket
          (SmoothForm.mpullback (Subtype.val : hξ.annihilatorPunctured → _) contMDiff_subtypeVal
            (mextDerivₗ (I.prod 𝓘(ℝ, Fin 1 → ℝ)) 1 hξ.annihilatorLiouvilleForm))
          (annihilatorPairing V ∘ Subtype.val) (annihilatorPairing W ∘ Subtype.val) z =
        annihilatorPairing (mlieBracket I (contactVectorField I ξ V) (contactVectorField I ξ W))
          (z : TotalSpace (Fin 1 → ℝ) fun x ↦ annihilatorSpace I ξ x) :=
  letI := hξ.isContMDiffDistribution.annihilatorFiberBundle hξ.finrank_sub_one_add_one
  haveI := hξ.isContMDiffDistribution.annihilatorVectorBundle hξ.finrank_sub_one_add_one
  haveI := hξ.isContMDiffDistribution.annihilatorContMDiffVectorBundle hξ.finrank_sub_one_add_one
  fun z ↦ by
  rw [SmoothTwoForm.poissonBracket_comp_subtype_val]
  exact hξ.poissonBracket_annihilatorPairing hV hW (hξ.mem_annihilatorPunctured.1 z.property)

end IsContactDistribution

end TauCeti
