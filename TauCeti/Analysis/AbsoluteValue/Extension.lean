/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import Mathlib.Analysis.AbsoluteValue.Equivalence
public import Mathlib.Analysis.Normed.Field.WithAbs
public import Mathlib.Analysis.Normed.Group.Ultra
public import Mathlib.Analysis.Normed.Unbundled.SpectralNorm
public import Mathlib.RingTheory.Artinian.Module
public import Mathlib.RingTheory.TensorProduct.Basic
import Mathlib.Analysis.Normed.Module.FiniteDimension
import TauCeti.Analysis.AbsoluteValue.Nonarchimedean
import TauCeti.Analysis.Normed.Field.WithAbs
import TauCeti.Analysis.Normed.Unbundled.SpectralNorm.FieldNorm
import TauCeti.RingTheory.NormTrace.BaseChange
import TauCeti.RingTheory.NormTrace.Pi

/-!
# Extensions of a nonarchimedean absolute value

For a finite field extension `L/K` and a nontrivial nonarchimedean absolute value `v` on
`K`, the absolute values on `L` restricting to `v` correspond to the maximal ideals of
`K_v ⊗[K] L`. The residue field at such an ideal is the corresponding completion of `L`.
The description uses the spectral norm on each residue field. When the completed scalar
extension is reduced, it is the product of these completions. The local degrees then sum
to `[L : K]` and the product of the degree-normalized extensions is the base absolute value
of the field norm. This is the normalization used for relative heights.

## References

* B. Conrad, *Chow's K/k-image and K/k-trace, and the Lang–Néron theorem*, §8, pp. 28–29.
-/

public section

open scoped TensorProduct

namespace AbsoluteValue.Completion

variable {K L : Type*} [Field K] [Field L] [Algebra K L]
  (v : AbsoluteValue K ℝ)

attribute [local instance] algebraOfLiesOver

variable {v} (w : AbsoluteValue L ℝ) [w.LiesOver v]

/-- The comparison from scalar extension to the completion at an absolute value extending
`v`. It sends `a ⊗ x` to the product of the images of `a` and `x`. -/
noncomputable def tensorToCompletion :
    v.Completion ⊗[K] L →ₐ[v.Completion] w.Completion :=
  AlgHom.liftEquiv K v.Completion L w.Completion
    { toRingHom := algebraMap L w.Completion
      commutes' x := by
        -- Expose the ring homomorphism application hidden by the structure literal.
        change algebraMap L w.Completion (algebraMap K L x) = algebraMap K w.Completion x
        rw [algebraMap_def, algebraMap_def, WithAbs.algebraMap_right_apply,
          WithAbs.algebraMap_right_apply, Algebra.algebraMap_self_apply] }

/-- The completion comparison multiplies the two scalar images on pure tensors. -/
@[simp]
theorem tensorToCompletion_tmul (a : v.Completion) (x : L) :
    tensorToCompletion w (a ⊗ₜ[K] x) =
      algebraMap v.Completion w.Completion a * algebraMap L w.Completion x := by
  rw [tensorToCompletion, AlgHom.liftEquiv_tmul, Algebra.smul_def]
  rfl

variable [FiniteDimensional K L]

/-- For a finite field extension, scalar extension onto a completion above `v` is surjective. -/
theorem tensorToCompletion_surjective (hv : v.IsNontrivial) :
    Function.Surjective (tensorToCompletion w (v := v)) := by
  let := nontriviallyNormedField v hv
  let := normedAlgebraOfLiesOver w (v := v)
  let f := (tensorToCompletion w (v := v)).toLinearMap
  have : FiniteDimensional v.Completion f.range := Module.Finite.range f
  have hd : Dense (f.range : Set w.Completion) :=
    (denseRange_algebraMap w).mono <| Set.range_subset_iff.mpr fun y ↦
      ⟨1 ⊗ₜ[K] y, by simp [f]⟩
  rw [dense_iff_closure_eq, f.range.isClosed_of_finiteDimensional.closure_eq] at hd
  exact LinearMap.range_eq_top.mp (SetLike.coe_injective hd)

/-- The completion at an extending absolute value is finite over the base completion. -/
theorem finiteDimensional_of_liesOver (hv : v.IsNontrivial) :
    FiniteDimensional v.Completion w.Completion :=
  Module.Finite.of_surjective (tensorToCompletion w).toLinearMap
    (tensorToCompletion_surjective w hv)

end AbsoluteValue.Completion

namespace AbsoluteValue

open Completion Algebra.TensorProduct

attribute [local instance] Completion.algebraOfLiesOver Ideal.Quotient.field

variable {K L : Type*} [Field K] [Field L] [Algebra K L] (v : AbsoluteValue K ℝ)

local notation "A" => v.Completion ⊗[K] L

private noncomputable def toFactor (m : MaximalSpectrum A) : L →+* A ⧸ m.asIdeal :=
  (Ideal.Quotient.mk m.asIdeal).comp (includeRight : L →ₐ[K] A).toRingHom

@[simp]
private theorem toFactor_apply (m : MaximalSpectrum A) (x : L) :
    toFactor v m x = Ideal.Quotient.mk m.asIdeal (1 ⊗ₜ[K] x) :=
  (rfl)

variable {v} [FiniteDimensional K L]

/-- The extension of a nonarchimedean absolute value obtained by pulling back the spectral norm
of the residue field at a maximal ideal of `K_v ⊗[K] L`. -/
noncomputable def ofCompletionFactor (hv : IsNonarchimedean v)
    (m : MaximalSpectrum A) : AbsoluteValue L ℝ :=
  letI := Completion.isUltrametricDist v hv
  letI := TauCeti.spectralNormedField v.Completion (A ⧸ m.asIdeal)
  (NormedField.toAbsoluteValue (A ⧸ m.asIdeal)).comp (f := toFactor v m) (toFactor v m).injective

/-- The extension given by a completion factor is computed by its spectral norm. -/
theorem ofCompletionFactor_apply (hv : IsNonarchimedean v) (m : MaximalSpectrum A) (x : L) :
    ofCompletionFactor hv m x =
      spectralNorm v.Completion (A ⧸ m.asIdeal) (Ideal.Quotient.mk m.asIdeal (1 ⊗ₜ[K] x)) := by
  simp only [ofCompletionFactor, AbsoluteValue.comp_apply, NormedField.toAbsoluteValue_apply,
    TauCeti.norm_spectralNormedField, toFactor_apply]

/-- The absolute value obtained from a completion factor restricts to the base absolute value. -/
instance liesOver_ofCompletionFactor (hv : IsNonarchimedean v) (m : MaximalSpectrum A) :
    (ofCompletionFactor hv m).LiesOver v := by
  refine ⟨AbsoluteValue.ext fun x ↦ ?_⟩
  rw [under_def, comp_apply, ofCompletionFactor_apply,
    ← Algebra.TensorProduct.algebraMap_apply', Ideal.Quotient.mk_algebraMap,
    IsScalarTower.algebraMap_apply K v.Completion (A ⧸ m.asIdeal),
    spectralNorm_extends, Completion.norm_algebraMap]

/-- The kernel of the map to the completion at an extension of `v`, as a maximal ideal of
`K_v ⊗[K] L`. -/
noncomputable def completionMaximalIdeal (hv : v.IsNontrivial)
    (w : AbsoluteValue L ℝ) [w.LiesOver v] : MaximalSpectrum A :=
  ⟨RingHom.ker (tensorToCompletion w (v := v)).toRingHom,
    RingHom.ker_isMaximal_of_surjective _ (tensorToCompletion_surjective w hv)⟩

/-- The ideal associated to an extending absolute value is the kernel of the comparison. -/
@[simp]
theorem completionMaximalIdeal_asIdeal (hv : v.IsNontrivial) (w : AbsoluteValue L ℝ)
    [w.LiesOver v] :
    (completionMaximalIdeal hv w).asIdeal = RingHom.ker (tensorToCompletion w).toRingHom :=
  (rfl)

/-- The residue field of the kernel of the completion comparison is the completion itself. -/
noncomputable def completionQuotientEquiv (hv : v.IsNontrivial)
    (w : AbsoluteValue L ℝ) [w.LiesOver v] :
    (A ⧸ (completionMaximalIdeal hv w).asIdeal) ≃ₐ[v.Completion] w.Completion :=
  Ideal.quotientKerAlgEquivOfSurjective (tensorToCompletion_surjective w hv)

/-- The quotient comparison sends a residue class to the image of its representative. -/
@[simp]
theorem completionQuotientEquiv_mk (hv : v.IsNontrivial) (w : AbsoluteValue L ℝ)
    [w.LiesOver v] (x : A) :
    completionQuotientEquiv hv w (Ideal.Quotient.mk _ x) = tensorToCompletion w x :=
  Ideal.quotientKerAlgEquivOfSurjective_mk _ x

/-- Recover an extending absolute value from the kernel of its completion comparison. -/
theorem ofCompletionFactor_completionMaximalIdeal (hv : v.IsNontrivial)
    (hna : IsNonarchimedean v) (w : AbsoluteValue L ℝ) [w.LiesOver v] :
    ofCompletionFactor hna (completionMaximalIdeal hv w) = w := by
  let := Completion.isUltrametricDist v hna
  let := Completion.normedAlgebraOfLiesOver w (v := v)
  let e := completionQuotientEquiv hv w
  have := finiteDimensional_of_liesOver w hv
  ext x
  rw [ofCompletionFactor_apply, ← e.toAlgHom.spectralNorm_map,
    AlgEquiv.coe_toAlgHom, completionQuotientEquiv_mk, tensorToCompletion_tmul,
    map_one, one_mul,
    ← TauCeti.norm_eq_spectralNorm v.Completion (Algebra.IsAlgebraic.isAlgebraic _),
    Completion.norm_algebraMap]

/-- The completion of the absolute value belonging to a factor recovers its maximal ideal. -/
theorem completionMaximalIdeal_ofCompletionFactor (hv : v.IsNontrivial)
    (hna : IsNonarchimedean v) (m : MaximalSpectrum A) :
    completionMaximalIdeal hv (ofCompletionFactor hna m) = m := by
  let := Completion.nontriviallyNormedField v hv
  let := Completion.isUltrametricDist v hna
  let F := A ⧸ m.asIdeal
  let : NormedField F := TauCeti.spectralNormedField v.Completion F
  let := TauCeti.spectralNormedAlgebra v.Completion F
  let : CompleteSpace F := FiniteDimensional.completeSpace v.Completion F
  let w := ofCompletionFactor hna m
  let f : WithAbs w →+* F := (toFactor v m).comp (WithAbs.equiv w).toRingHom
  have hf : Isometry f := AddMonoidHomClass.isometry_of_norm _ fun y ↦ by
    rw [WithAbs.norm_eq_apply_ofAbs, ofCompletionFactor_apply, TauCeti.norm_spectralNormedField]
    rfl
  let G := (UniformSpace.Completion.extensionHom f hf.continuous).comp
    (Completion.toCompletion (v := w))
  have hG : Continuous G :=
    UniformSpace.Completion.continuous_extension.comp (continuous_toCompletion w)
  have hGcoe (x : L) : G (algebraMap L w.Completion x) = toFactor v m x := by
    rw [Completion.algebraMap_def, WithAbs.algebraMap_right_apply, Algebra.algebraMap_self_apply,
      RingHom.comp_apply, toCompletion_coe, UniformSpace.Completion.extensionHom_coe]
    simp [f]
  have hscalar : (G : w.Completion →+* F).comp (map v w) = algebraMap v.Completion F := by
    refine DFunLike.ext' (Completion.ext (hG.comp (continuous_map v w))
      (continuous_algebraMap _ _) fun x ↦ ?_)
    have hx : algebraMap L w.Completion (algebraMap K L x.ofAbs) =
        (WithAbs.map v w (algebraMap K L) x : w.Completion) := by
      rw [Completion.algebraMap_def, WithAbs.algebraMap_right_apply, Algebra.algebraMap_self_apply,
        WithAbs.map_apply]
    rw [RingHom.comp_apply, map_coe, ← hx, hGcoe]
    -- The scalar and the element of L represent the same tensor over K.
    rw [toFactor_apply, ← Algebra.TensorProduct.algebraMap_apply',
      IsScalarTower.algebraMap_apply K v.Completion A, Ideal.Quotient.mk_algebraMap,
      Completion.algebraMap_def, WithAbs.algebraMap_right_apply,
      Algebra.algebraMap_self_apply, WithAbs.toAbs_ofAbs]
  have hcomp : G.comp (tensorToCompletion w (v := v)).toRingHom = Ideal.Quotient.mk m.asIdeal := by
    apply Algebra.TensorProduct.ringHom_ext
    · ext a
      have ha : Ideal.Quotient.mk m.asIdeal (a ⊗ₜ[K] (1 : L)) =
          algebraMap v.Completion F a := by
        rw [← Ideal.Quotient.mk_algebraMap (R₁ := v.Completion),
          Algebra.TensorProduct.algebraMap_apply, Algebra.algebraMap_self_apply]
      simpa [tensorToCompletion_tmul, algebraMap_apply_of_liesOver, ha] using
        DFunLike.congr_fun hscalar a
    · ext x
      simpa [tensorToCompletion_tmul] using hGcoe x
  apply MaximalSpectrum.ext
  refine (completionMaximalIdeal hv w).isMaximal.eq_of_le m.isMaximal.ne_top fun x hx ↦ ?_
  rw [← Ideal.Quotient.eq_zero_iff_mem, ← hcomp, RingHom.comp_apply]
  exact (congrArg G (RingHom.mem_ker.mp hx)).trans (map_zero G)

/-- Maximal ideals of the completed scalar extension classify the absolute values on `L`
restricting to the given nontrivial nonarchimedean absolute value on `K`. -/
noncomputable def maximalSpectrumEquivLiesOver (hv : v.IsNontrivial)
    (hna : IsNonarchimedean v) : MaximalSpectrum A ≃ {w : AbsoluteValue L ℝ // w.LiesOver v} where
  toFun m := ⟨ofCompletionFactor hna m, inferInstance⟩
  invFun w := by
    letI := w.property
    exact completionMaximalIdeal hv w.val
  left_inv m := completionMaximalIdeal_ofCompletionFactor hv hna m
  right_inv w := by
    have := w.property
    exact Subtype.ext (ofCompletionFactor_completionMaximalIdeal hv hna _)

/-- The forward correspondence takes the spectral norm of the residue field. -/
@[simp]
theorem maximalSpectrumEquivLiesOver_apply (hv : v.IsNontrivial)
    (hna : IsNonarchimedean v) (m : MaximalSpectrum A) :
    (maximalSpectrumEquivLiesOver hv hna m).val = ofCompletionFactor hna m :=
  (rfl)

/-- The inverse correspondence takes the kernel of the completion comparison. -/
@[simp]
theorem maximalSpectrumEquivLiesOver_symm_apply (hv : v.IsNontrivial)
    (hna : IsNonarchimedean v) (w : AbsoluteValue L ℝ) [hw : w.LiesOver v] :
    (maximalSpectrumEquivLiesOver hv hna).symm ⟨w, hw⟩ = completionMaximalIdeal hv w :=
  (rfl)

/-- A finite field extension has only finitely many absolute values restricting to a given
nontrivial nonarchimedean absolute value. -/
theorem finite_liesOver (hv : v.IsNontrivial) (hna : IsNonarchimedean v) :
    Finite {w : AbsoluteValue L ℝ // w.LiesOver v} := by
  let : IsArtinianRing A := IsArtinianRing.of_finite v.Completion A
  exact Finite.of_equiv _ (maximalSpectrumEquivLiesOver hv hna)

/-- The height normalization of an extension of a nonarchimedean absolute value raises it to
its local degree. -/
noncomputable def degreeNormalized (w : AbsoluteValue L ℝ) [w.LiesOver v]
    (hv : v.IsNontrivial) (hna : IsNonarchimedean v) : AbsoluteValue L ℝ :=
  w.nonarchRpow (isNonarchimedean_of_liesOver hna) (t := w.degree K) (by
    have := finiteDimensional_of_liesOver w hv
    rw [Nat.cast_pos, degree_eq v w]
    exact Module.finrank_pos)

/-- Evaluate the degree-normalized extension as an ordinary natural power. -/
@[simp]
theorem degreeNormalized_apply (w : AbsoluteValue L ℝ) [w.LiesOver v]
    (hv : v.IsNontrivial) (hna : IsNonarchimedean v) (x : L) :
    w.degreeNormalized (v := v) hv hna x = w x ^ w.degree K := by
  rw [degreeNormalized, nonarchRpow_apply, Real.rpow_natCast]

/-- The normalized extension restricts to the base absolute value raised to the local degree. -/
theorem degreeNormalized_algebraMap (w : AbsoluteValue L ℝ) [w.LiesOver v]
    (hv : v.IsNontrivial) (hna : IsNonarchimedean v) (x : K) :
    w.degreeNormalized (v := v) hv hna (algebraMap K L x) = v x ^ w.degree K := by
  rw [degreeNormalized_apply, LiesOver.apply_algebraMap v]

/-- Degree normalization preserves the equivalence class of the extending absolute value. -/
theorem isEquiv_degreeNormalized (w : AbsoluteValue L ℝ) [w.LiesOver v]
    (hv : v.IsNontrivial) (hna : IsNonarchimedean v) :
    w.IsEquiv (w.degreeNormalized (v := v) hv hna) := by
  rw [degreeNormalized]
  exact isEquiv_nonarchRpow _ _ _

/-- A degree-normalized extension of a nonarchimedean absolute value remains nonarchimedean. -/
theorem isNonarchimedean_degreeNormalized (w : AbsoluteValue L ℝ) [w.LiesOver v]
    (hv : v.IsNontrivial) (hna : IsNonarchimedean v) :
    IsNonarchimedean (w.degreeNormalized (v := v) hv hna) := by
  rw [degreeNormalized]
  exact isNonarchimedean_nonarchRpow _ _ _

/-- An absolute value in the subtype of absolute values over `v` lies over `v`. -/
instance instLiesOverSubtype (w : {w : AbsoluteValue L ℝ // w.LiesOver v}) :
    w.val.LiesOver v := w.property

section Reduced

variable [IsReduced (v.Completion ⊗[K] L)]

/-- If the scalar extension of `L` to the completion at `v` is reduced, it is the product of
the completions of `L` at the absolute values restricting to `v`. -/
noncomputable def semilocalEquiv (hv : v.IsNontrivial) (hna : IsNonarchimedean v) :
    A ≃ₐ[v.Completion] (w : {w : AbsoluteValue L ℝ // w.LiesOver v}) → w.val.Completion :=
  letI : IsArtinianRing A := IsArtinianRing.of_finite v.Completion A
  let e := maximalSpectrumEquivLiesOver (L := L) hv hna
  ((IsArtinianRing.equivPi A).restrictScalars v.Completion).trans <|
    (AlgEquiv.piCongrLeft' v.Completion (fun m : MaximalSpectrum A ↦ A ⧸ m.asIdeal) e).trans <|
      AlgEquiv.piCongrRight fun w ↦ completionQuotientEquiv hv w.val

/-- Each coordinate of the product decomposition is the comparison to that completion. -/
@[simp]
theorem semilocalEquiv_apply (hv : v.IsNontrivial) (hna : IsNonarchimedean v)
    (y : A) (w : {w : AbsoluteValue L ℝ // w.LiesOver v}) :
    semilocalEquiv hv hna y w = tensorToCompletion w.val y := by
  simp only [semilocalEquiv, AlgEquiv.trans_apply, AlgEquiv.restrictScalars_apply,
    AlgEquiv.piCongrLeft'_apply]
  exact completionQuotientEquiv_mk hv w.val y

/-- The local degrees over a nonarchimedean absolute value add up to the global degree when
the completed scalar extension is reduced. -/
theorem finsum_degree_liesOver (hv : v.IsNontrivial) (hna : IsNonarchimedean v) :
    ∑ᶠ w : {w : AbsoluteValue L ℝ // w.LiesOver v}, w.val.degree K = Module.finrank K L := by
  have := finite_liesOver (L := L) hv hna
  let : Fintype {w : AbsoluteValue L ℝ // w.LiesOver v} := Fintype.ofFinite _
  let (w : {w : AbsoluteValue L ℝ // w.LiesOver v}) :
      FiniteDimensional v.Completion w.val.Completion := finiteDimensional_of_liesOver w.val hv
  simp_rw [finsum_eq_sum_of_fintype, degree_eq v]
  rw [← Module.finrank_pi_fintype, ← (semilocalEquiv (L := L) hv hna).toLinearEquiv.finrank_eq,
    Module.finrank_baseChange]

/-- The product of the degree-normalized extensions evaluated at an element of `L` equals
the value of its field norm at the base absolute value. -/
theorem finprod_degreeNormalized_eq (hv : v.IsNontrivial) (hna : IsNonarchimedean v) (x : L) :
    ∏ᶠ w : {w : AbsoluteValue L ℝ // w.LiesOver v}, w.val.degreeNormalized (v := v) hv hna x =
      v (Algebra.norm K x) := by
  have := finite_liesOver (L := L) hv hna
  let : Fintype {w : AbsoluteValue L ℝ // w.LiesOver v} := Fintype.ofFinite _
  let (w : {w : AbsoluteValue L ℝ // w.LiesOver v}) :
      FiniteDimensional v.Completion w.val.Completion := finiteDimensional_of_liesOver w.val hv
  let := Completion.isUltrametricDist v hna
  rw [finprod_eq_prod_of_fintype, ← Completion.norm_algebraMap,
    ← TauCeti.Algebra.norm_baseChange_tmul, ← Algebra.norm_eq_of_algEquiv (semilocalEquiv hv hna),
    TauCeti.Algebra.norm_pi, norm_prod]
  refine Finset.prod_congr rfl fun w _ ↦ ?_
  let := Completion.normedAlgebraOfLiesOver w.val (v := v)
  rw [semilocalEquiv_apply, tensorToCompletion_tmul, map_one, one_mul,
    TauCeti.norm_algebraNorm_eq_spectralNorm_pow_finrank, degreeNormalized_apply, degree_eq v w.val,
    ← TauCeti.norm_eq_spectralNorm v.Completion (Algebra.IsAlgebraic.isAlgebraic _),
    Completion.norm_algebraMap]

end Reduced

end AbsoluteValue
