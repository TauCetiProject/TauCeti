/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.Geometry.Manifold.Morse.Deformation
public import TauCeti.Geometry.Manifold.RegularValue.Level
import Mathlib.Geometry.Manifold.Algebra.LieGroup
import TauCeti.Geometry.Manifold.MFDeriv.NormedSpace
import TauCeti.Geometry.Manifold.SmoothEmbedding.Basic

/-!
# The smooth product structure of a band without critical points

Let `f` be a smooth real function on a boundaryless finite-dimensional manifold `M`, and let
`a ≤ b` be such that the band `f⁻¹[a, b]` is compact and consists of regular points of `f`.
Following the lines of a flow along which `f` decreases at unit speed through the band down to the
level `f⁻¹(a)` is a homeomorphism `f⁻¹[a, b] ≃ₜ f⁻¹(a) × [a, b]` preserving the value of `f`
(`TauCeti.exists_bandHomeomorph`). This file shows that it is smooth wherever both sides carry
smooth structures, for the atlas `TauCeti.regularLevelChartedSpace` of the regular levels.

* On the open band `{a < f < b}`, an open subset of `M`, it is a diffeomorphism onto the product
  manifold `f⁻¹(a) × (a, b)` (`Flow.bandInteriorDiffeomorph`).
* On each level `f⁻¹(s)`, `a ≤ s ≤ b`, its first component is a diffeomorphism of regular levels
  `f⁻¹(s) ≃ f⁻¹(a)` (`Flow.bandLevelDiffeomorph`). For `s = a` it is the identity, and for
  `s = b` it identifies the two boundary levels of the band.

Both are built from a flow `φ` which is jointly smooth in time and space and lowers `f` at unit
speed through the band, as provided by `TauCeti.exists_flow_apply_eq_sub`; their inverses run the
flow backwards. The inverse of the interior diffeomorphism is `(y, t) ↦ φ (a - t) y`. The smooth
structures on the corners `f⁻¹(a) × {a, b}` of the product are not compared here: no cornered model
is identified with the half-space model of the band.

## Main declarations

* `Flow.bandLevelDiffeomorph`: the diffeomorphism `f⁻¹(s) ≃ f⁻¹(a)`, `x ↦ φ (s - a) x`.
* `Flow.bandInteriorDiffeomorph`: the diffeomorphism `{a < f < b} ≃ f⁻¹(a) × (a, b)`,
  `x ↦ (φ (f x - a) x, f x)`.
* `TauCeti.exists_bandHomeomorph_diffeomorph`: the product homeomorphism of a compact band without
  critical points, with its smooth restrictions to the open band and to each level.

## References

* J. Milnor, *Lectures on the h-cobordism theorem*, Princeton University Press, 1965,
  Theorem 3.4.
* J. Milnor, *Morse Theory*, Annals of Mathematics Studies 51, Princeton University Press, 1963,
  Theorem 3.1.
-/

public section

open Function Module Set TauCeti TopologicalSpace
open scoped ContDiff Manifold

variable {E H M : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E] [FiniteDimensional ℝ E]
  [TopologicalSpace H] {I : ModelWithCorners ℝ E H} [I.Boundaryless]
  [TopologicalSpace M] [ChartedSpace H M] [IsManifold I ∞ M] {f : M → ℝ} {a b s : ℝ} {n : ℕ}

namespace Flow

section

variable (φ : Flow ℝ M) (hφ : ContMDiff (𝓘(ℝ, ℝ).prod I) I ∞ (fun p : ℝ × M ↦ φ p.1 p.2))
  (hf : ContMDiff I 𝓘(ℝ) ∞ f) (hanti : ∀ x, AntitoneOn (fun t ↦ f (φ t x)) (Ici 0))
  (hφf : ∀ x t, 0 ≤ t → a ≤ f x - t → f x ≤ b → f (φ t x) = f x - t)
  (hφa : ∀ x t, f x = a → 0 < t → f (φ t x) < a)
  (hn : finrank ℝ E - finrank ℝ ℝ = n)

/-- **The levels of a band traversed at unit speed are diffeomorphic.** Let `φ` be a flow, jointly
smooth in time and space, along whose lines `f` never increases in positive time, and which lowers
`f` at unit speed through the band `a ≤ f ≤ b`. For a regular value `s` of `f` in `[a, b]`, its
time-`(s - a)` map carries the regular level `f⁻¹(s)` diffeomorphically onto the regular level
`f⁻¹(a)`, for the atlases `TauCeti.regularLevelChartedSpace`. The inverse is the time-`(a - s)` map
of `φ`. -/
noncomputable def bandLevelDiffeomorph (has : a ≤ s) (hsb : s ≤ b)
    (hrega : IsRegularValue I 𝓘(ℝ) f a) (hregs : IsRegularValue I 𝓘(ℝ) f s) :
    letI := regularLevelChartedSpace (fun _ _ ↦ hf.contMDiffAt.of_le (by simp)) hregs hn
    letI := regularLevelChartedSpace (fun _ _ ↦ hf.contMDiffAt.of_le (by simp)) hrega hn
    {x : M // f x = s} ≃ₘ⟮𝓘(ℝ, Fin n → ℝ), 𝓘(ℝ, Fin n → ℝ)⟯ {x : M // f x = a} :=
  letI := regularLevelChartedSpace (fun _ _ ↦ hf.contMDiffAt.of_le (by simp)) hregs hn
  letI := regularLevelChartedSpace (fun _ _ ↦ hf.contMDiffAt.of_le (by simp)) hrega hn
  have hdown (x : {x : M // f x = s}) : f (φ (s - a) x) = a := by
    rw [hφf x _ (sub_nonneg.2 has) (by rw [x.2]; linarith) (x.2.trans_le hsb), x.2]
    ring
  have hup (y : {x : M // f x = a}) : f (φ (a - s) y) = s := by
    rw [← neg_sub, φ.apply_neg_eq_add_of_apply_eq_sub hf.continuous hanti hφf hφa y.2
      (sub_nonneg.2 has) (by linarith), add_sub_cancel]
  { toFun x := ⟨φ (s - a) x, hdown x⟩
    invFun y := ⟨φ (a - s) y, hup y⟩
    left_inv x := Subtype.ext <| by
      dsimp only
      rw [← Flow.map_add, sub_add_sub_cancel, sub_self, Flow.map_zero_apply]
    right_inv y := Subtype.ext <| by
      dsimp only
      rw [← Flow.map_add, sub_add_sub_cancel, sub_self, Flow.map_zero_apply]
    contMDiff_toFun := (isSmoothEmbedding_coe_regularLevel (by simp) (fun _ _ ↦ hf.contMDiffAt)
        hrega hn).contMDiff_iff_comp.2 <| (hφ.comp (contMDiff_const.prodMk contMDiff_id)).comp
          (isSmoothEmbedding_coe_regularLevel (by simp) (fun _ _ ↦ hf.contMDiffAt) hregs
            hn).contMDiff
    contMDiff_invFun := (isSmoothEmbedding_coe_regularLevel (by simp) (fun _ _ ↦ hf.contMDiffAt)
        hregs hn).contMDiff_iff_comp.2 <| (hφ.comp (contMDiff_const.prodMk contMDiff_id)).comp
          (isSmoothEmbedding_coe_regularLevel (by simp) (fun _ _ ↦ hf.contMDiffAt) hrega
            hn).contMDiff }

@[simp]
theorem coe_bandLevelDiffeomorph_apply (has : a ≤ s) (hsb : s ≤ b)
    (hrega : IsRegularValue I 𝓘(ℝ) f a) (hregs : IsRegularValue I 𝓘(ℝ) f s)
    (x : {x : M // f x = s}) :
    letI := regularLevelChartedSpace (fun _ _ ↦ hf.contMDiffAt.of_le (by simp)) hregs hn
    letI := regularLevelChartedSpace (fun _ _ ↦ hf.contMDiffAt.of_le (by simp)) hrega hn
    (φ.bandLevelDiffeomorph hφ hf hanti hφf hφa hn has hsb hrega hregs x : M) = φ (s - a) x :=
  (rfl)

@[simp]
theorem coe_bandLevelDiffeomorph_symm_apply (has : a ≤ s) (hsb : s ≤ b)
    (hrega : IsRegularValue I 𝓘(ℝ) f a) (hregs : IsRegularValue I 𝓘(ℝ) f s)
    (y : {x : M // f x = a}) :
    letI := regularLevelChartedSpace (fun _ _ ↦ hf.contMDiffAt.of_le (by simp)) hregs hn
    letI := regularLevelChartedSpace (fun _ _ ↦ hf.contMDiffAt.of_le (by simp)) hrega hn
    ((φ.bandLevelDiffeomorph hφ hf hanti hφf hφa hn has hsb hrega hregs).symm y : M) =
      φ (a - s) y :=
  (rfl)

/-- **The open band traversed at unit speed is a product.** Let `φ` be a flow, jointly smooth in
time and space, along whose lines `f` never increases in positive time, and which lowers `f` at
unit speed through the band `a ≤ f ≤ b`. If `a` is a regular value of `f`, following each point
`x` of the open band `{a < f < b}` down its flow line to the level `f⁻¹(a)` is a diffeomorphism
`x ↦ (φ (f x - a) x, f x)` onto the product of the regular level `f⁻¹(a)`, with its atlas
`TauCeti.regularLevelChartedSpace`, and the interval `(a, b)`. The inverse is
`(y, t) ↦ φ (a - t) y`. -/
noncomputable def bandInteriorDiffeomorph (hrega : IsRegularValue I 𝓘(ℝ) f a) :
    letI := regularLevelChartedSpace (fun _ _ ↦ hf.contMDiffAt.of_le (by simp)) hrega hn
    (⟨f ⁻¹' Ioo a b, isOpen_Ioo.preimage hf.continuous⟩ : Opens M) ≃ₘ⟮I,
      𝓘(ℝ, Fin n → ℝ).prod 𝓘(ℝ, ℝ)⟯ {x : M // f x = a} × (⟨Ioo a b, isOpen_Ioo⟩ : Opens ℝ) :=
  letI := regularLevelChartedSpace (fun _ _ ↦ hf.contMDiffAt.of_le (by simp)) hrega hn
  have hmem (x : (⟨f ⁻¹' Ioo a b, isOpen_Ioo.preimage hf.continuous⟩ : Opens M)) :
      f x ∈ Ioo a b :=
    mem_preimage.1 (Opens.mem_mk.1 x.2)
  have hdown (x : (⟨f ⁻¹' Ioo a b, isOpen_Ioo.preimage hf.continuous⟩ : Opens M)) :
      f (φ (f x - a) x) = a := by
    rw [hφf x _ (by linarith [(hmem x).1]) (by linarith) (hmem x).2.le]
    ring
  have hup (p : {x : M // f x = a} × (⟨Ioo a b, isOpen_Ioo⟩ : Opens ℝ)) :
      f (φ (a - p.2) p.1) = p.2 := by
    have hp : (p.2 : ℝ) ∈ Ioo a b := Opens.mem_mk.1 p.2.2
    rw [← neg_sub, φ.apply_neg_eq_add_of_apply_eq_sub hf.continuous hanti hφf hφa p.1.2
      (by linarith [hp.1]) (by linarith [hp.2]), add_sub_cancel]
  { toFun x := (⟨φ (f x - a) x, hdown x⟩, ⟨f x, Opens.mem_mk.2 (hmem x)⟩)
    invFun p := ⟨φ (a - p.2) p.1, by rw [Opens.mem_mk, mem_preimage, hup p]; exact p.2.2⟩
    left_inv x := Subtype.ext <| by
      dsimp only
      rw [← Flow.map_add, sub_add_sub_cancel, sub_self, Flow.map_zero_apply]
    right_inv p := Prod.ext (Subtype.ext <| by
        dsimp only
        rw [hup p, ← Flow.map_add, sub_add_sub_cancel, sub_self, Flow.map_zero_apply])
      (Subtype.ext (hup p))
    contMDiff_toFun := by
      have hemb := isSmoothEmbedding_coe_regularLevel (by simp) (fun _ _ ↦ hf.contMDiffAt) hrega hn
      refine ContMDiff.prodMk (hemb.contMDiff_iff_comp.2 ?_)
        ((ContMDiff.subtypeVal_comp_iff _ _).1 (hf.comp contMDiff_subtype_val))
      exact hφ.comp (((hf.comp contMDiff_subtype_val).sub contMDiff_const).prodMk
        contMDiff_subtype_val)
    contMDiff_invFun := by
      have hemb := isSmoothEmbedding_coe_regularLevel (by simp) (fun _ _ ↦ hf.contMDiffAt) hrega hn
      refine (ContMDiff.subtypeVal_comp_iff _ _).1 ?_
      exact hφ.comp ((contMDiff_const.sub (contMDiff_subtype_val.comp contMDiff_snd)).prodMk
        (hemb.contMDiff.comp contMDiff_fst)) }

@[simp]
theorem coe_bandInteriorDiffeomorph_apply_fst (hrega : IsRegularValue I 𝓘(ℝ) f a)
    (x : (⟨f ⁻¹' Ioo a b, isOpen_Ioo.preimage hf.continuous⟩ : Opens M)) :
    letI := regularLevelChartedSpace (fun _ _ ↦ hf.contMDiffAt.of_le (by simp)) hrega hn
    ((φ.bandInteriorDiffeomorph hφ hf hanti hφf hφa hn hrega x).1 : M) = φ (f x - a) x :=
  (rfl)

@[simp]
theorem coe_bandInteriorDiffeomorph_apply_snd (hrega : IsRegularValue I 𝓘(ℝ) f a)
    (x : (⟨f ⁻¹' Ioo a b, isOpen_Ioo.preimage hf.continuous⟩ : Opens M)) :
    letI := regularLevelChartedSpace (fun _ _ ↦ hf.contMDiffAt.of_le (by simp)) hrega hn
    ((φ.bandInteriorDiffeomorph hφ hf hanti hφf hφa hn hrega x).2 : ℝ) = f x :=
  (rfl)

@[simp]
theorem coe_bandInteriorDiffeomorph_symm_apply (hrega : IsRegularValue I 𝓘(ℝ) f a)
    (p : {x : M // f x = a} × (⟨Ioo a b, isOpen_Ioo⟩ : Opens ℝ)) :
    letI := regularLevelChartedSpace (fun _ _ ↦ hf.contMDiffAt.of_le (by simp)) hrega hn
    ((φ.bandInteriorDiffeomorph hφ hf hanti hφf hφa hn hrega).symm p : M) = φ (a - p.2) p.1 :=
  (rfl)

end

end Flow

namespace TauCeti

/-- **A band without critical points is a smooth product** (Milnor, *Lectures on the h-cobordism
theorem*, Theorem 3.4). Let `f` be smooth, `a ≤ b`, and let the band `f⁻¹[a, b]` be compact with
every value in `[a, b]` a regular value of `f`. Then there is a homeomorphism
`e : f⁻¹[a, b] ≃ₜ f⁻¹(a) × [a, b]` whose second component is the value of `f` and which is the
identity on the level `f⁻¹(a)`, such that, for the atlases `TauCeti.regularLevelChartedSpace` of
the regular levels,

* on the open band `{a < f < b}`, `e` is a diffeomorphism onto `f⁻¹(a) × (a, b)`;
* on each level `f⁻¹(s)`, `a ≤ s ≤ b`, the first component of `e` is a diffeomorphism
  `f⁻¹(s) ≃ f⁻¹(a)`. -/
theorem exists_bandHomeomorph_diffeomorph [T2Space M] (hf : ContMDiff I 𝓘(ℝ) ∞ f) (hab : a ≤ b)
    (hcompact : IsCompact (f ⁻¹' Icc a b)) (hreg : ∀ s ∈ Icc a b, IsRegularValue I 𝓘(ℝ) f s)
    (hn : finrank ℝ E - finrank ℝ ℝ = n) :
    letI := regularLevelChartedSpace (fun _ _ ↦ hf.contMDiffAt.of_le (by simp))
      (hreg a ⟨le_rfl, hab⟩) hn
    ∃ e : f ⁻¹' Icc a b ≃ₜ (f ⁻¹' {a}) × Icc a b,
      (∀ x, ((e x).2 : ℝ) = f x) ∧ (∀ x : f ⁻¹' Icc a b, f x = a → ((e x).1 : M) = x) ∧
      (∃ Ψ : (⟨f ⁻¹' Ioo a b, isOpen_Ioo.preimage hf.continuous⟩ : Opens M) ≃ₘ⟮I,
          𝓘(ℝ, Fin n → ℝ).prod 𝓘(ℝ, ℝ)⟯ {x : M // f x = a} × (⟨Ioo a b, isOpen_Ioo⟩ : Opens ℝ),
        ∀ x, ((Ψ x).1 : M) = (e ⟨x, preimage_mono Ioo_subset_Icc_self (Opens.mem_mk.1 x.2)⟩).1 ∧
          ((Ψ x).2 : ℝ) = f x) ∧
      ∀ s (hs : s ∈ Icc a b),
        letI := regularLevelChartedSpace (fun _ _ ↦ hf.contMDiffAt.of_le (by simp)) (hreg s hs) hn
        ∃ g : {x : M // f x = s} ≃ₘ⟮𝓘(ℝ, Fin n → ℝ), 𝓘(ℝ, Fin n → ℝ)⟯ {x : M // f x = a},
          ∀ x : {x : M // f x = s}, (g x : M) = (e ⟨x, by rw [mem_preimage, x.2]; exact hs⟩).1 := by
  have hreg' (x : M) (hxa : a ≤ f x) (hxb : f x ≤ b) : mfderiv I 𝓘(ℝ) f x ≠ 0 :=
    mvfderiv_eq_zero_iff.not.1
      (isRegularPoint_iff_mvfderiv_ne_zero.1 ((hreg _ ⟨hxa, hxb⟩).isRegularPoint rfl))
  obtain ⟨φ, hφ, hanti, hlt, hφf⟩ := exists_flow_apply_eq_sub hf hcompact hreg'
  have hanti' : ∀ x, AntitoneOn (fun t ↦ f (φ t x)) (Ici 0) := fun x ↦ (hanti x).antitoneOn _
  have hφa : ∀ x t, f x = a → 0 < t → f (φ t x) < a := fun x t hx ht ↦
    (hlt x t hx.ge (hx.trans_le hab) ht).trans_eq hx
  refine ⟨φ.bandHomeomorph hf.continuous hanti' hφf hφa,
    φ.coe_bandHomeomorph_apply_snd hf.continuous hanti' hφf hφa,
    fun _ hx ↦ φ.coe_bandHomeomorph_apply_fst_of_apply_eq hf.continuous hanti' hφf hφa hx,
    ⟨φ.bandInteriorDiffeomorph hφ hf hanti' hφf hφa hn _, fun x ↦ ⟨?_, ?_⟩⟩,
    fun s hs ↦ ⟨φ.bandLevelDiffeomorph hφ hf hanti' hφf hφa hn hs.1 hs.2 _ _, fun x ↦ ?_⟩⟩
  · rw [Flow.coe_bandInteriorDiffeomorph_apply_fst, Flow.coe_bandHomeomorph_apply_fst]
  · rw [Flow.coe_bandInteriorDiffeomorph_apply_snd]
  · rw [Flow.coe_bandLevelDiffeomorph_apply, Flow.coe_bandHomeomorph_apply_fst, x.2]

end TauCeti
