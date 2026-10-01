/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import Mathlib.Analysis.InnerProductSpace.l2Space
public import Mathlib.MeasureTheory.Function.AEEqOfIntegral
public import Mathlib.MeasureTheory.Function.L2Space
public import Mathlib.MeasureTheory.Integral.Pi
public import TauCeti.MeasureTheory.Integral.PiSystem

/-!
# Pointwise products of `L²` functions on a finite product measure

For a finite family of σ-finite measures `μ i` and `L²(μ i)` functions `f i`, the pointwise product
`x ↦ ∏ i, f i (x i)` belongs to `L²(Measure.pi μ)`, the assignment factors the inner product as a
tensor, and coordinatewise Hilbert bases multiply to a Hilbert basis `TauCeti.piHilbertBasis` of
`L²(Measure.pi μ)`. This is the `Fintype`-indexed analogue of the binary product basis
`TauCeti.prodHilbertBasis`.

## Main definitions

* `TauCeti.L2piMul` — the pointwise product `x ↦ ∏ i, F i (x i)` as a vector of `L²(Measure.pi μ)`.
* `TauCeti.piHilbertBasis` — the Hilbert basis of `L²(Measure.pi μ)` built from coordinatewise
  Hilbert bases.

## Main statements

* `TauCeti.memLp_pi_prod` — the pointwise product of `L²` functions is `L²` for the product measure.
* `TauCeti.integrable_L2piMul_mul` — a product of `L²` factors times an `L²` function is integrable.
* `TauCeti.inner_L2piMul` — the inner product of two tensors factors coordinatewise.
* `TauCeti.orthonormal_L2piMul` — coordinatewise orthonormal families multiply to an orthonormal
  family.
* `TauCeti.orthogonal_span_range_L2piMul_eq_bot` — the basis tensors have trivial orthogonal
  complement.
* `TauCeti.piHilbertBasis_apply`, `TauCeti.coeFn_piHilbertBasis` — the `k`-th basis vector is the
  tensor of the `k i`-th coordinate basis vectors, a.e. equal to `∏ i, b i (k i)`.
* `TauCeti.piHilbertBasis_repr_L2piMul` — the coordinates of a tensor are the products of its
  coordinatewise coordinates.

## Implementation notes

Orthonormality follows from Mathlib's Fubini theorem `integral_fintype_prod_eq_prod`.
Completeness assumes no countability of the index types `κ i` and runs in three steps:

1. `TauCeti.inner_L2piMul_eq_zero_of_forall_basis` — orthogonality to the *basis* tensors upgrades
   to orthogonality to *every* elementary tensor, by `Finset` induction on the coordinates, pushing
   a basis expansion of one slot through the continuous linear map `TauCeti.L2piMulSlot`.
2. `TauCeti.setIntegral_pi_eq_zero_of_forall_inner` — testing against indicators, since a tensor of
   indicators is the indicator of the box.
3. `TauCeti.setIntegral_eq_zero_of_forall_inner_pi` — the Dynkin (π-λ) step
   `TauCeti.setIntegral_eq_zero_of_isPiSystem` applied to `isPiSystem_pi` inside a finite box,
   followed by a monotone exhaustion along `∏ i, spanningSets (μ i) n`.
-/

public section

namespace TauCeti

open MeasureTheory

variable {𝕜 ι : Type*} [Fintype ι] {α : ι → Type*}
  [∀ i, MeasurableSpace (α i)] {μ : ∀ i, Measure (α i)} [∀ i, SigmaFinite (μ i)]

section NormedCommRing

variable [NormedCommRing 𝕜]

/-- The pointwise product `x ↦ ∏ i, f i (x i)` of `L²` functions is `L²` for the product measure. -/
theorem memLp_pi_prod {f : ∀ i, α i → 𝕜} (hf : ∀ i, MemLp (f i) 2 (μ i)) :
    MemLp (fun x : ∀ i, α i => ∏ i, f i (x i)) 2 (Measure.pi μ) := by
  have hmeas : AEStronglyMeasurable (fun x : ∀ i, α i => ∏ i, f i (x i)) (Measure.pi μ) :=
    Finset.aestronglyMeasurable_fun_prod (f := fun i (x : ∀ j, α j) => f i (x i)) _ fun i _ =>
      (hf i).aestronglyMeasurable.comp_quasiMeasurePreserving
        (Measure.quasiMeasurePreserving_eval μ i)
  rw [memLp_two_iff_integrable_sq_norm hmeas]
  rcases isEmpty_or_nonempty ι with hι | hι
  · -- With no coordinates the integrand is constant and the product measure is a Dirac mass.
    have : IsProbabilityMeasure (Measure.pi μ) := by rw [Measure.pi_of_empty]; infer_instance
    simp
  -- Only the submultiplicative bound `‖∏ aᵢ‖ ≤ ∏ ‖aᵢ‖` is needed, so the norm need not be
  -- multiplicative; `Finset.norm_prod_le'` gives it for a nonempty index without `‖1‖ = 1`.
  refine (Integrable.fintype_prod_dep fun i =>
    (memLp_two_iff_integrable_sq_norm (hf i).aestronglyMeasurable).1 (hf i)).mono'
    (hmeas.norm.pow 2) (.of_forall fun x => ?_)
  rw [Real.norm_of_nonneg (by positivity), Finset.prod_pow]
  gcongr
  exact Finset.norm_prod_le' _ Finset.univ_nonempty _

/-- The pointwise product `x ↦ ∏ i, F i (x i)` of a family of `L²(μ i)` vectors, as a vector of
`L²(Measure.pi μ)`. -/
noncomputable def L2piMul (F : ∀ i, Lp 𝕜 2 (μ i)) : Lp 𝕜 2 (Measure.pi μ) :=
  (memLp_pi_prod (fun i => Lp.memLp (F i))).toLp _

/-- The `Lp` representative of `L2piMul F` is the pointwise product of the representatives. -/
theorem coeFn_L2piMul (F : ∀ i, Lp 𝕜 2 (μ i)) :
    ⇑(L2piMul F) =ᵐ[Measure.pi μ] fun x : ∀ i, α i => ∏ i, F i (x i) :=
  MemLp.coeFn_toLp _

/-- A pointwise product of coordinatewise `L²` functions times an `L²` function on the product
space is integrable. -/
theorem integrable_L2piMul_mul (F : ∀ i, Lp 𝕜 2 (μ i)) (f : Lp 𝕜 2 (Measure.pi μ)) :
    Integrable (fun x : ∀ i, α i => (∏ i, F i (x i)) * f x) (Measure.pi μ) :=
  (memLp_pi_prod fun i => Lp.memLp (F i)).integrable_mul (Lp.memLp f)

section Slot

variable [DecidableEq ι]

/-- Splitting off the `j`-th coordinate of a tensor. -/
theorem coeFn_L2piMul_update (j : ι) (F : ∀ i, Lp 𝕜 2 (μ i)) (v : Lp 𝕜 2 (μ j)) :
    ⇑(L2piMul (Function.update F j v)) =ᵐ[Measure.pi μ]
      fun x : ∀ i, α i => v (x j) * ∏ i ∈ Finset.univ.erase j, F i (x i) := by
  filter_upwards [coeFn_L2piMul (Function.update F j v)] with x hx
  rw [hx, ← Finset.mul_prod_erase _ _ (Finset.mem_univ j), Function.update_self]
  simp +contextual [Finset.prod_congr rfl, Function.update_of_ne]

/-- The tensor is additive in the `j`-th coordinate. -/
@[simp]
theorem L2piMul_update_add (j : ι) (F : ∀ i, Lp 𝕜 2 (μ i)) (v w : Lp 𝕜 2 (μ j)) :
    L2piMul (Function.update F j (v + w))
      = L2piMul (Function.update F j v) + L2piMul (Function.update F j w) := by
  rw [Lp.ext_iff]
  filter_upwards [coeFn_L2piMul_update j F (v + w), coeFn_L2piMul_update j F v,
    coeFn_L2piMul_update j F w,
    Lp.coeFn_add (L2piMul (Function.update F j v)) (L2piMul (Function.update F j w)),
    (Measure.quasiMeasurePreserving_eval μ j).tendsto_ae.eventually (Lp.coeFn_add v w)]
    with x h h1 h2 hadd hv
  rw [h, hadd, Pi.add_apply, h1, h2, hv, Pi.add_apply, add_mul]

/-- The tensor is homogeneous in the `j`-th coordinate. -/
@[simp]
theorem L2piMul_update_smul (j : ι) (F : ∀ i, Lp 𝕜 2 (μ i)) (c : 𝕜) (v : Lp 𝕜 2 (μ j)) :
    L2piMul (Function.update F j (c • v)) = c • L2piMul (Function.update F j v) := by
  rw [Lp.ext_iff]
  filter_upwards [coeFn_L2piMul_update j F (c • v), coeFn_L2piMul_update j F v,
    Lp.coeFn_smul c (L2piMul (Function.update F j v)),
    (Measure.quasiMeasurePreserving_eval μ j).tendsto_ae.eventually (Lp.coeFn_smul c v)]
    with x h h1 hsmul hv
  rw [h, hsmul, Pi.smul_apply, h1, hv, Pi.smul_apply, smul_eq_mul, smul_eq_mul, mul_assoc]

/-- The tensor vanishes when its `j`-th coordinate does. -/
@[simp]
theorem L2piMul_update_zero (j : ι) (F : ∀ i, Lp 𝕜 2 (μ i)) :
    L2piMul (Function.update F j 0) = 0 := by
  simpa using L2piMul_update_smul j F 0 0

end Slot

end NormedCommRing

variable [RCLike 𝕜]

/-- **The tensor inner-product identity, `Fintype`-indexed.** The inner product of two pointwise
products factors as the product of the coordinatewise inner products. -/
@[simp]
theorem inner_L2piMul (F G : ∀ i, Lp 𝕜 2 (μ i)) :
    inner 𝕜 (L2piMul F) (L2piMul G) = ∏ i, inner 𝕜 (F i) (G i) := by
  rw [L2.inner_def]
  calc
    ∫ x, inner 𝕜 (L2piMul F x) (L2piMul G x) ∂(Measure.pi μ)
        = ∫ x : ∀ i, α i, ∏ i, inner 𝕜 (F i (x i)) (G i (x i)) ∂(Measure.pi μ) := by
          refine integral_congr_ae ?_
          filter_upwards [coeFn_L2piMul F, coeFn_L2piMul G] with x hF hG
          rw [hF, hG]
          simp only [RCLike.inner_apply', map_prod, Finset.prod_mul_distrib]
    _ = ∏ i, ∫ x, inner 𝕜 (F i x) (G i x) ∂(μ i) :=
          integral_fintype_prod_eq_prod (fun i x => inner 𝕜 (F i x) (G i x))
    _ = ∏ i, inner 𝕜 (F i) (G i) :=
          Finset.prod_congr rfl fun i _ => (L2.inner_def _ _).symm

/-- **Orthonormality of the tensor family, `Fintype`-indexed.** Coordinatewise orthonormal families
multiply to an orthonormal family of `L²(Measure.pi μ)`, indexed by the dependent function type. -/
theorem orthonormal_L2piMul {κ : ι → Type*} {b : ∀ i, κ i → Lp 𝕜 2 (μ i)}
    (hb : ∀ i, Orthonormal 𝕜 (b i)) :
    Orthonormal 𝕜 (fun k : ∀ i, κ i => L2piMul (fun i => b i (k i))) := by
  classical
  simp_rw [orthonormal_iff_ite] at hb ⊢
  simp [hb, Fintype.prod_boole, funext_iff]

/-- The tensor construction is norm-multiplicative. -/
@[simp]
theorem norm_L2piMul (F : ∀ i, Lp 𝕜 2 (μ i)) : ‖L2piMul F‖ = ∏ i, ‖F i‖ := by
  rw [← sq_eq_sq₀ (norm_nonneg _) (by positivity), ← Finset.prod_pow]
  exact_mod_cast (by simpa only [inner_self_eq_norm_sq_to_K] using inner_L2piMul F F :
    ((‖L2piMul F‖ : ℝ) : 𝕜) ^ 2 = ∏ i, ((‖F i‖ : ℝ) : 𝕜) ^ 2)

section Slot

variable [DecidableEq ι]

/-- The norm of a tensor with its `j`-th coordinate replaced. -/
theorem norm_L2piMul_update (j : ι) (F : ∀ i, Lp 𝕜 2 (μ i)) (v : Lp 𝕜 2 (μ j)) :
    ‖L2piMul (Function.update F j v)‖ = (∏ i ∈ Finset.univ.erase j, ‖F i‖) * ‖v‖ := by
  rw [norm_L2piMul, ← Finset.mul_prod_erase _ _ (Finset.mem_univ j), Function.update_self, mul_comm]
  simp +contextual [Finset.prod_congr rfl, Function.update_of_ne]

/-- Tensoring with all coordinates but `j` held fixed, as a continuous linear map. -/
noncomputable def L2piMulSlot (j : ι) (F : ∀ i, Lp 𝕜 2 (μ i)) :
    Lp 𝕜 2 (μ j) →L[𝕜] Lp 𝕜 2 (Measure.pi μ) :=
  LinearMap.mkContinuous
    { toFun := fun v => L2piMul (Function.update F j v)
      map_add' := L2piMul_update_add j F
      map_smul' := fun c v => L2piMul_update_smul j F c v }
    (∏ i ∈ Finset.univ.erase j, ‖F i‖) fun v => le_of_eq (norm_L2piMul_update j F v)

/-- `L2piMulSlot` applies as the tensor. -/
@[simp]
theorem L2piMulSlot_apply (j : ι) (F : ∀ i, Lp 𝕜 2 (μ i)) (v : Lp 𝕜 2 (μ j)) :
    L2piMulSlot j F v = L2piMul (Function.update F j v) :=
  LinearMap.mkContinuous_apply _ _ _ _

end Slot

/-- **Basis tensors detect all tensors.** A vector orthogonal to every tensor built from
coordinatewise Hilbert bases is orthogonal to *every* elementary tensor. -/
theorem inner_L2piMul_eq_zero_of_forall_basis {κ : ι → Type*}
    (b : ∀ i, HilbertBasis (κ i) 𝕜 (Lp 𝕜 2 (μ i))) {h : Lp 𝕜 2 (Measure.pi μ)}
    (hz : ∀ k : ∀ i, κ i, inner 𝕜 h (L2piMul (fun i => b i (k i))) = 0)
    (F : ∀ i, Lp 𝕜 2 (μ i)) : inner 𝕜 h (L2piMul F) = 0 := by
  classical
  -- Induct on the set `S` of coordinates allowed to be arbitrary; the rest are basis vectors.
  suffices key : ∀ S : Finset ι, ∀ F : ∀ i, Lp 𝕜 2 (μ i),
      (∀ i ∉ S, ∃ c, F i = b i c) → inner 𝕜 h (L2piMul F) = 0 from
    key Finset.univ F (by simp)
  intro S
  induction S using Finset.induction with
  | empty =>
      intro F hF
      choose k hk using fun i => hF i (Finset.notMem_empty i)
      simpa [← funext hk] using hz k
  | @insert j S hj ih =>
      intro F hF
      -- Expand the `j`-th coordinate along `b j` and push the sum through a continuous linear map.
      have hzero : HasSum (fun _ : κ j => (0 : 𝕜))
          ((innerSL 𝕜 h).comp (L2piMulSlot j F) (F j)) := by
        refine (((b j).hasSum_repr (F j)).mapL _).congr_fun fun c => ?_
        have hupd : inner 𝕜 h (L2piMul (Function.update F j (b j c))) = 0 := by
          refine ih _ fun i hi => ?_
          rcases eq_or_ne i j with rfl | hij
          · exact ⟨c, Function.update_self ..⟩
          · simpa [hij] using hF i (by simp [hij, hi])
        simp [hupd]
      simpa using (hasSum_zero.unique hzero).symm

/-- A vector orthogonal to every elementary tensor has vanishing integral over every box whose
sides are measurable sets of finite measure. -/
theorem setIntegral_pi_eq_zero_of_forall_inner {h : Lp 𝕜 2 (Measure.pi μ)}
    (hz : ∀ F : ∀ i, Lp 𝕜 2 (μ i), inner 𝕜 (L2piMul F) h = 0)
    (s : ∀ i, Set (α i)) (hs : ∀ i, MeasurableSet (s i)) (hfin : ∀ i, μ i (s i) ≠ ⊤) :
    ∫ x in Set.univ.pi s, h x ∂(Measure.pi μ) = 0 := by
  set F : ∀ i, Lp 𝕜 2 (μ i) := fun i => indicatorConstLp 2 (hs i) (hfin i) (1 : 𝕜)
  have hFc : ∀ᵐ x : ∀ i, α i ∂(Measure.pi μ),
      ∀ i, F i (x i) = (s i).indicator (fun _ => (1 : 𝕜)) (x i) := by
    rw [ae_all_iff]
    exact fun i => (Measure.quasiMeasurePreserving_eval μ i).tendsto_ae.eventually
      indicatorConstLp_coeFn
  calc ∫ x in Set.univ.pi s, h x ∂(Measure.pi μ)
      = ∫ x, (Set.univ.pi s).indicator (fun y => h y) x ∂(Measure.pi μ) :=
        (integral_indicator (MeasurableSet.univ_pi hs)).symm
    _ = ∫ x, inner 𝕜 ((L2piMul F) x) (h x) ∂(Measure.pi μ) := by
        refine integral_congr_ae ?_
        filter_upwards [coeFn_L2piMul F, hFc] with x hx hF
        classical
        simp [hx, hF, Set.indicator_apply, Fintype.prod_boole]
    _ = inner 𝕜 (L2piMul F) h := (L2.inner_def _ _).symm
    _ = 0 := hz F

/-- Orthogonality to every elementary tensor makes the integral of `h` vanish on the intersection
of any measurable set with a product box of spanning sets. -/
private theorem setIntegral_inter_univ_pi_spanningSets_eq_zero {h : Lp 𝕜 2 (Measure.pi μ)}
    (hz : ∀ F : ∀ i, Lp 𝕜 2 (μ i), inner 𝕜 (L2piMul F) h = 0) {u : Set (∀ i, α i)}
    (hu : MeasurableSet u) (n : ℕ) :
    ∫ x in u ∩ (Set.univ.pi fun i => spanningSets (μ i) n), h x ∂(Measure.pi μ) = 0 := by
  classical
  have hboxfin : Measure.pi μ (Set.univ.pi fun i => spanningSets (μ i) n) < ⊤ := by
    rw [Measure.pi_pi]
    exact ENNReal.prod_lt_top fun i _ => measure_spanningSets_lt_top (μ i) n
  have huniv : ∫ x, h x ∂((Measure.pi μ).restrict
      (Set.univ.pi fun i => spanningSets (μ i) n)) = 0 :=
    setIntegral_pi_eq_zero_of_forall_inner hz _ (fun i => measurableSet_spanningSets (μ i) n)
      (fun i => (measure_spanningSets_lt_top (μ i) n).ne)
  have hS : ∀ t ∈ (Set.pi Set.univ '' Set.pi Set.univ fun i => {v : Set (α i) | MeasurableSet v}),
      ∫ x in t, h x ∂((Measure.pi μ).restrict
        (Set.univ.pi fun i => spanningSets (μ i) n)) = 0 := by
    rintro _ ⟨t, ht, rfl⟩
    rw [Measure.restrict_restrict
      (MeasurableSet.univ_pi fun i => ht i (Set.mem_univ i)), ← Set.pi_inter_distrib]
    exact setIntegral_pi_eq_zero_of_forall_inner hz _
      (fun i => (ht i (Set.mem_univ i)).inter (measurableSet_spanningSets (μ i) n))
      (fun i => (lt_of_le_of_lt (measure_mono Set.inter_subset_right)
        (measure_spanningSets_lt_top (μ i) n)).ne)
  have hdyn := setIntegral_eq_zero_of_isPiSystem generateFrom_pi.symm isPiSystem_pi
    (integrableOn_Lp_of_measure_ne_top h one_le_two hboxfin.ne) huniv hS u hu
  rwa [Measure.restrict_restrict hu] at hdyn

/-- A vector orthogonal to every elementary tensor has vanishing integral over every measurable set
of finite measure. -/
theorem setIntegral_eq_zero_of_forall_inner_pi {h : Lp 𝕜 2 (Measure.pi μ)}
    (hz : ∀ F : ∀ i, Lp 𝕜 2 (μ i), inner 𝕜 (L2piMul F) h = 0)
    (u : Set (∀ i, α i)) (hu : MeasurableSet u) (hfin : Measure.pi μ u < ⊤) :
    ∫ x in u, h x ∂(Measure.pi μ) = 0 := by
  have hmono : Monotone fun n => u ∩ (Set.univ.pi fun i => spanningSets (μ i) n) := fun m n hmn =>
    Set.inter_subset_inter_right _ (Set.pi_mono fun i _ => monotone_spanningSets (μ i) hmn)
  have hcover : ⋃ n, u ∩ (Set.univ.pi fun i => spanningSets (μ i) n) = u := by
    rw [← Set.inter_iUnion,
      Set.iUnion_univ_pi_of_monotone fun i => monotone_spanningSets (μ i)]
    simp [iUnion_spanningSets, Set.pi_univ]
  have htend := tendsto_setIntegral_of_monotone
    (fun n => hu.inter (MeasurableSet.univ_pi fun i => measurableSet_spanningSets (μ i) n)) hmono
    (by rw [hcover]; exact integrableOn_Lp_of_measure_ne_top h one_le_two hfin.ne)
  rw [hcover] at htend
  simp only [setIntegral_inter_univ_pi_spanningSets_eq_zero hz hu] at htend
  exact tendsto_nhds_unique htend tendsto_const_nhds

/-- **Completeness of the tensor family.** The tensors built from coordinatewise Hilbert bases have
trivial orthogonal complement in `L²(Measure.pi μ)`. -/
theorem orthogonal_span_range_L2piMul_eq_bot {κ : ι → Type*}
    (b : ∀ i, HilbertBasis (κ i) 𝕜 (Lp 𝕜 2 (μ i))) :
    (Submodule.span 𝕜 (Set.range fun k : ∀ i, κ i => L2piMul fun i => b i (k i)))ᗮ = ⊥ := by
  refine (Submodule.eq_bot_iff _).2 fun h hh => ?_
  rw [Submodule.mem_orthogonal] at hh
  have hz : ∀ F : ∀ i, Lp 𝕜 2 (μ i), inner 𝕜 (L2piMul F) h = 0 := by
    intro F
    rw [inner_eq_zero_symm]
    refine inner_L2piMul_eq_zero_of_forall_basis b (fun k => ?_) F
    rw [inner_eq_zero_symm]
    exact hh _ (Submodule.subset_span ⟨k, rfl⟩)
  have hae := Lp.ae_eq_zero_of_forall_setIntegral_eq_zero h (by norm_num) (by norm_num)
    (fun s _ hs' => integrableOn_Lp_of_measure_ne_top h one_le_two hs'.ne)
    (fun s hs hs' => setIntegral_eq_zero_of_forall_inner_pi hz s hs hs')
  rw [Lp.ext_iff]
  exact hae.trans (Lp.coeFn_zero 𝕜 2 (Measure.pi μ)).symm

/-- **The `Fintype`-indexed product Hilbert basis.** Pointwise products of coordinatewise Hilbert
bases form a Hilbert basis of `L²(Measure.pi μ)`, indexed by the dependent function type. -/
noncomputable def piHilbertBasis {κ : ι → Type*} (b : ∀ i, HilbertBasis (κ i) 𝕜 (Lp 𝕜 2 (μ i))) :
    HilbertBasis (∀ i, κ i) 𝕜 (Lp 𝕜 2 (Measure.pi μ)) :=
  HilbertBasis.mkOfOrthogonalEqBot (orthonormal_L2piMul fun i => (b i).orthonormal)
    (orthogonal_span_range_L2piMul_eq_bot b)

/-- The `k`-th vector of `piHilbertBasis` is the tensor of the `k i`-th basis vectors. -/
@[simp]
theorem piHilbertBasis_apply {κ : ι → Type*}
    (b : ∀ i, HilbertBasis (κ i) 𝕜 (Lp 𝕜 2 (μ i))) (k : ∀ i, κ i) :
    piHilbertBasis b k = L2piMul fun i => b i (k i) := by
  rw [piHilbertBasis, HilbertBasis.coe_mkOfOrthogonalEqBot]

/-- The coordinate of a tensor in a product Hilbert basis is the product of its coordinatewise
coordinates. -/
@[simp]
theorem piHilbertBasis_repr_L2piMul {κ : ι → Type*}
    (b : ∀ i, HilbertBasis (κ i) 𝕜 (Lp 𝕜 2 (μ i))) (F : ∀ i, Lp 𝕜 2 (μ i))
    (k : ∀ i, κ i) :
    (piHilbertBasis b).repr (L2piMul F) k = ∏ i, (b i).repr (F i) (k i) := by
  rw [HilbertBasis.repr_apply_apply, piHilbertBasis_apply, inner_L2piMul]
  exact Finset.prod_congr rfl fun i _ => (HilbertBasis.repr_apply_apply (b i) (F i) (k i)).symm

/-- The `k`-th vector of `piHilbertBasis` is a.e. the pointwise product `∏ i, b i (k i)`. -/
theorem coeFn_piHilbertBasis {κ : ι → Type*}
    (b : ∀ i, HilbertBasis (κ i) 𝕜 (Lp 𝕜 2 (μ i))) (k : ∀ i, κ i) :
    ⇑(piHilbertBasis b k) =ᵐ[Measure.pi μ] fun x : ∀ i, α i => ∏ i, b i (k i) (x i) := by
  rw [piHilbertBasis_apply]
  exact coeFn_L2piMul _

end TauCeti
