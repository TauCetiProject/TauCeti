/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import Mathlib.Topology.Algebra.Module.ContinuousLinearMap.Invertible
public import Mathlib.Topology.Algebra.Module.Equiv.Prod
public import Mathlib.Topology.Algebra.Module.Spaces.ContinuousLinearMap
public import TauCeti.Topology.Algebra.Module.Equiv.SMul
import Mathlib.Tactic.Abel

/-!
# Invertibility of continuous linear maps: persistence, products, and completeness

The totalized inverse of a continuous linear map is zero when the map is not invertible.
Consequently, convergence of inverse maps to any nonzero map forces eventual invertibility.
The inverse of an invertible map also suffices, including on trivial spaces. These results apply
without completeness or continuity of the original family, and are useful when differentiating
inverse families.

Over a field, multiplying a map by a nonzero scalar `c` preserves invertibility, and the inverse
of `c • f` is `c⁻¹ • f.inverse`; this is how the inverse of a positively homogeneous family of
maps is seen to be homogeneous of the opposite degree.

The file also records that the product `f.prodMap g` of two continuous linear maps is invertible
exactly when both factors are, which is how block-diagonal second derivatives on a product space
are shown to be invertible. More generally, a map `M₁ × M₂ → M₁ × M₃` which preserves the first
coordinate is block lower triangular, and it is invertible exactly when its diagonal block
`M₂ → M₃` is. This is the shape of the differential of a fibre-preserving map between vector
bundles over the same base, read in bundle charts.

Between uniformly topologized modules an invertible continuous linear map transfers
completeness from the codomain to the domain, because its inverse is a uniform homeomorphism.

The rectangular Jacobson identity says that `1 - u ∘ v` and `1 - v ∘ u` are invertible together,
even for maps between different modules. It transports invertibility from an operator to its
extension through a continuous linear retract, without any choice of complementary submodule.
-/

public section

open Filter
open scoped Topology

namespace ContinuousLinearMap

section CompleteSpace

variable {R E F : Type*} [Semiring R]
  [UniformSpace E] [AddCommGroup E] [IsUniformAddGroup E] [Module R E]
  [UniformSpace F] [AddCommGroup F] [IsUniformAddGroup F] [Module R F]

/-- The domain of an invertible continuous linear map between uniformly topologized modules is
complete when the codomain is: its inverse is a uniform homeomorphism. -/
theorem completeSpace_of_isInvertible [CompleteSpace F] {f : E →L[R] F} (hf : f.IsInvertible) :
    CompleteSpace E := by
  obtain ⟨e, _⟩ := hf
  exact (e.isUniformEmbedding.completeSpace_congr e.surjective).mpr inferInstance

end CompleteSpace

variable {𝕜 E F ι : Type*} [NormedField 𝕜]
  [AddCommGroup E] [Module 𝕜 E] [TopologicalSpace E] [IsTopologicalAddGroup E] [T2Space E]
  [AddCommGroup F] [Module 𝕜 F] [TopologicalSpace F] [ContinuousSMul 𝕜 F]

/-- If the inverses of a family converge to a nonzero map, then the family is eventually
invertible. Convergence uses the topology of bounded convergence; neither completeness nor
convergence of the original family is required. -/
theorem eventually_isInvertible_of_tendsto_inverse {A : ι → E →L[𝕜] F} {B : F →L[𝕜] E}
    {l : Filter ι} (h : Tendsto (fun i => (A i).inverse) l (𝓝 B)) (hB : B ≠ 0) :
    ∀ᶠ i in l, (A i).IsInvertible := by
  filter_upwards [h.eventually_ne hB] with i hi
  by_contra hA
  exact hi (inverse_of_not_isInvertible hA)

/-- If the inverses of a family converge to the inverse of an invertible map, then the family
is eventually invertible. Convergence uses the topology of bounded convergence; neither
completeness nor convergence of the original family is required. -/
theorem IsInvertible.eventually_of_tendsto_inverse {A : ι → E →L[𝕜] F} {B : E →L[𝕜] F}
    (hB : B.IsInvertible) {l : Filter ι}
    (h : Tendsto (fun i => (A i).inverse) l (𝓝 B.inverse)) :
    ∀ᶠ i in l, (A i).IsInvertible := by
  by_cases hzero : B.inverse = 0
  · -- Then the zero map `F → E` is invertible, so both spaces are trivial.
    obtain ⟨hF, hE⟩ := isInvertible_zero_iff.mp (hzero ▸ hB.inverse)
    exact Eventually.of_forall fun i ↦
      Subsingleton.elim 0 (A i) ▸ isInvertible_zero_iff.mpr ⟨hE, hF⟩
  · exact eventually_isInvertible_of_tendsto_inverse h hzero

section Smul

variable {𝕜 M M₂ : Type*} [Field 𝕜]
  [TopologicalSpace M] [AddCommMonoid M] [Module 𝕜 M] [ContinuousConstSMul 𝕜 M]
  [TopologicalSpace M₂] [AddCommMonoid M₂] [Module 𝕜 M₂] [ContinuousConstSMul 𝕜 M₂]

omit [ContinuousConstSMul 𝕜 M] in
/-- Multiplying a continuous linear map by a nonzero scalar does not change its
invertibility. -/
@[simp]
theorem isInvertible_smul_iff {c : 𝕜} (hc : c ≠ 0) {f : M →L[𝕜] M₂} :
    (c • f).IsInvertible ↔ f.IsInvertible := by
  rw [smul_eq_smulLeft_comp hc, isInvertible_equiv_comp]

/-- The inverse of `c • f` is `c⁻¹ • f.inverse`. This holds for every scalar: both sides vanish
when `c = 0` or when `f` is not invertible. -/
theorem inverse_smul (c : 𝕜) (f : M →L[𝕜] M₂) : (c • f).inverse = c⁻¹ • f.inverse := by
  rcases eq_or_ne c 0 with rfl | hc
  · -- `zero_smul` is unavailable here: `M →L[𝕜] M₂` is a `𝕜`-module only under
    -- `ContinuousAdd M₂`, which these lemmas do not assume.
    have h0 : (0 : 𝕜) • f = 0 := by ext; simp
    ext y
    simp [h0]
  rw [smul_eq_smulLeft_comp hc, inverse_equiv_comp]
  ext y
  rw [comp_apply, ContinuousLinearEquiv.coe_coe,
    (ContinuousLinearEquiv.symm_apply_eq _ (y := c⁻¹ • y)).2 (by simp [smul_smul, hc]),
    map_smul, smul_apply]

end Smul

section ProdMap

variable {R M₁ M₂ M₃ M₄ : Type*} [Semiring R]
  [TopologicalSpace M₁] [AddCommMonoid M₁] [Module R M₁]
  [TopologicalSpace M₂] [AddCommMonoid M₂] [Module R M₂]
  [TopologicalSpace M₃] [AddCommMonoid M₃] [Module R M₃]
  [TopologicalSpace M₄] [AddCommMonoid M₄] [Module R M₄]

/-- The product `f.prodMap g` of two continuous linear maps is invertible exactly when both
factors are. -/
@[simp]
theorem isInvertible_prodMap_iff {f : M₁ →L[R] M₂} {g : M₃ →L[R] M₄} :
    (f.prodMap g).IsInvertible ↔ f.IsInvertible ∧ g.IsInvertible := by
  constructor
  · intro h
    -- The inverse of `f` is read off the first coordinate of the inverse of `f.prodMap g` on the
    -- first factor, and similarly for `g`.
    refine ⟨IsInvertible.of_inverse (g := fst R M₁ M₃ ∘L (f.prodMap g).inverse ∘L inl R M₂ M₄)
      ?_ ?_, IsInvertible.of_inverse (g := snd R M₁ M₃ ∘L (f.prodMap g).inverse ∘L inr R M₂ M₄)
      ?_ ?_⟩
    · ext v
      simpa using congrArg Prod.fst (h.self_apply_inverse (inl R M₂ M₄ v))
    · ext v
      simpa using congrArg Prod.fst (h.inverse_apply_self (v, 0))
    · ext v
      simpa using congrArg Prod.snd (h.self_apply_inverse (inr R M₂ M₄ v))
    · ext v
      simpa using congrArg Prod.snd (h.inverse_apply_self (0, v))
  · rintro ⟨⟨e, rfl⟩, ⟨e', rfl⟩⟩
    exact ⟨e.prodCongr e', ContinuousLinearEquiv.coe_prodCongr e e'⟩

end ProdMap

section FstPreserving

variable {R M₁ M₂ M₃ : Type*} [Semiring R]
  [TopologicalSpace M₁] [AddCommGroup M₁] [Module R M₁]
  [TopologicalSpace M₂] [AddCommGroup M₂] [Module R M₂]
  [TopologicalSpace M₃] [AddCommGroup M₃] [Module R M₃] [IsTopologicalAddGroup M₃]

/-- A continuous linear map `T : M₁ × M₂ → M₁ × M₃` which preserves the first coordinate is block
lower triangular, `T (a, b) = (a, C a + K b)`, so it is invertible exactly when its diagonal block
`K = snd ∘ T ∘ inr : M₂ → M₃` is. -/
theorem isInvertible_iff_of_fst_comp_eq {T : M₁ × M₂ →L[R] M₁ × M₃}
    (hT : fst R M₁ M₃ ∘L T = fst R M₁ M₂) :
    T.IsInvertible ↔ (snd R M₁ M₃ ∘L T ∘L inr R M₁ M₂).IsInvertible := by
  have hfst (p : M₁ × M₂) : (T p).1 = p.1 := DFunLike.congr_fun hT p
  constructor
  · intro h
    -- The inverse of `T` also preserves the first coordinate, so its diagonal block inverts that
    -- of `T`.
    have hinv (q : M₁ × M₃) : (T.inverse q).1 = q.1 := by
      rw [← hfst, h.self_apply_inverse]
    refine IsInvertible.of_inverse (g := snd R M₁ M₂ ∘L T.inverse ∘L inr R M₁ M₃) ?_ ?_
    · ext c
      have hq : T.inverse (0, c) = (0, (T.inverse (0, c)).2) := Prod.ext (hinv _) rfl
      have := congrArg Prod.snd (h.self_apply_inverse (0, c))
      rw [hq] at this
      simpa using this
    · ext b
      have hq : T (0, b) = (0, (T (0, b)).2) := Prod.ext (hfst _) rfl
      have := congrArg Prod.snd (h.inverse_apply_self (0, b))
      rw [hq] at this
      simpa using this
  · rintro ⟨K, hK⟩
    refine ⟨(ContinuousLinearEquiv.refl R M₁).skewProd K (snd R M₁ M₃ ∘L T ∘L inl R M₁ M₂), ?_⟩
    refine ContinuousLinearMap.ext fun p ↦ Prod.ext ?_ ?_
    · simp [hfst]
    · have hp : p = (p.1, 0) + (0, p.2) := by simp
      have hKp : K p.2 = (T (0, p.2)).2 := DFunLike.congr_fun hK p.2
      conv_rhs => rw [hp, map_add]
      simp [hKp, add_comm]

end FstPreserving

section OneSubComp

variable {R M N : Type*} [Ring R]
  [TopologicalSpace M] [AddCommGroup M] [Module R M] [IsTopologicalAddGroup M]
  [TopologicalSpace N] [AddCommGroup N] [Module R N] [IsTopologicalAddGroup N]

private theorem isUnit_one_sub_comp_of (u : N →L[R] M) (v : M →L[R] N)
    (h : IsUnit (1 - v.comp u)) : IsUnit (1 - u.comp v) := by
  obtain ⟨t, ht, ht'⟩ := isUnit_iff_exists.mp h
  -- Both identities for `1 + u ∘ t ∘ v` are `u` applied to those for `t` at `v x`, rearranged.
  refine isUnit_iff_exists.mpr ⟨1 + u.comp (t.comp v), ?_, ?_⟩ <;> ext x
  · have := sub_eq_zero.mpr (congrArg u (DFunLike.congr_fun ht (v x)))
    simp only [mul_apply_eq_comp, sub_apply, add_apply, one_apply_eq_self, comp_apply, map_add,
      map_sub] at this ⊢
    exact sub_eq_zero.mp (.trans (by abel) this)
  · have := sub_eq_zero.mpr (congrArg u (DFunLike.congr_fun ht' (v x)))
    simp only [mul_apply_eq_comp, sub_apply, add_apply, one_apply_eq_self, comp_apply,
      map_sub] at this ⊢
    exact sub_eq_zero.mp (.trans (by abel) this)

/-- The rectangular Jacobson identity: for maps between two topological modules,
`1 - u ∘ v` is invertible exactly when `1 - v ∘ u` is invertible. -/
theorem isUnit_one_sub_comp_comm (u : N →L[R] M) (v : M →L[R] N) :
    IsUnit (1 - u.comp v) ↔ IsUnit (1 - v.comp u) :=
  ⟨isUnit_one_sub_comp_of v u, isUnit_one_sub_comp_of u v⟩

end OneSubComp

end ContinuousLinearMap
