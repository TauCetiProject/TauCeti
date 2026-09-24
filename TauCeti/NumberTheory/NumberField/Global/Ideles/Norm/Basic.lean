/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import Mathlib.Topology.Algebra.Group.Units
public import TauCeti.NumberTheory.NumberField.Global.Ideles.Basic
public import TauCeti.NumberTheory.NumberField.Global.Places.Basic
public import TauCeti.NumberTheory.NumberField.Global.Places.Completion

/-!
# The idele norm of a number field

An idele of a number field `K` is a unit `x` of the adele ring `𝔸_K`
(`NumberField.IdeleGroup (𝓞 K) K`).  Its coordinate `x_v` at every place is a unit of the
completion `K_v`, and at all but finitely many finite places it is a unit of the valuation ring.
The **idele norm** is the product of the normalized local absolute values of the coordinates,
```
‖x‖ = ∏_{w | ∞} |x_w|_w · ∏_{v < ∞} ‖x_v‖_v,
```
where `|·|_w` is the absolute value at a real place and its square at a complex place
(`infiniteCompletionNormalizedAbsValue`), and `‖·‖_v` is the norm of the `v`-adic completion, which
sends a uniformizer to `(N v)⁻¹`.  Almost every finite factor is `1`, so the product is a finite
one.  The idele norm is a group homomorphism to the positive reals, and the product formula says
exactly that it is trivial on the principal ideles, which is what lets it descend to the idele
class group.

## Main definitions

* `IsDedekindDomain.HeightOneSpectrum.ideleFiniteCoord`: the coordinate of an idele at a finite
  place, as a homomorphism to the units of the `v`-adic completion.
* `NumberField.InfinitePlace.ideleInfiniteCoord`: the coordinate of an idele at an infinite place,
  as a homomorphism to the units of the archimedean completion.
* `TauCeti.GlobalNumberFields.ideleNorm`: the idele norm, a homomorphism to `ℝ≥0ˣ`.

## Main results

* `TauCeti.GlobalNumberFields.eventually_norm_ideleFiniteCoord_eq_one`: the finite coordinates of
  an idele have norm `1` at all but finitely many places.
* `TauCeti.GlobalNumberFields.coe_ideleNorm`: the idele norm is the product of the normalized local
  absolute values of the coordinates.
* `TauCeti.GlobalNumberFields.ideleNorm_unitEmbedding`: the idele norm of a principal idele is `1`;
  this is the product formula `NumberField.prod_abs_eq_one`, read on ideles.
* `TauCeti.GlobalNumberFields.principalSubgroup_le_ker_ideleNorm`: the principal ideles lie in the
  kernel of the idele norm.
* `TauCeti.GlobalNumberFields.coe_ideleNorm_ofAdicCompletion`,
  `TauCeti.GlobalNumberFields.coe_ideleNorm_ofCompletion`: on an idele concentrated at one place
  the idele norm is the normalized absolute value at that place.
* `TauCeti.GlobalNumberFields.continuous_ideleNorm`: the idele norm is continuous, because the
  finite factors are locally constant on the idele group.
* `TauCeti.GlobalNumberFields.ideleNorm_surjective`: every positive real number is an idele norm.

## References

* J. W. S. Cassels and A. Fröhlich, eds., *Algebraic Number Theory*, Chapter II, §16.
* J. Neukirch, *Algebraic Number Theory*, Chapter VI, §1.
* J. Tate, *Fourier analysis in number fields and Hecke's zeta-functions*, §3.3.
-/

public section
noncomputable section

open IsDedekindDomain NumberField
open scoped NNReal

variable {K : Type*} [Field K]

/-! ### Coordinates of an idele -/

section Coordinates

variable {R : Type*} [CommRing R] [IsDedekindDomain R] [Algebra R K] [IsFractionRing R K]

/-- The coordinate of an idele at a finite place `v`, a unit of the `v`-adic completion. -/
def IsDedekindDomain.HeightOneSpectrum.ideleFiniteCoord (v : HeightOneSpectrum R) :
    IdeleGroup R K →* (v.adicCompletion K)ˣ :=
  Units.map <| (RestrictedProduct.evalMonoidHom _ v).comp
    (MonoidHom.snd (InfiniteAdeleRing K) (FiniteAdeleRing R K))

/-- The coordinate of an idele at an infinite place `w`, a unit of the completion at `w`. -/
def NumberField.InfinitePlace.ideleInfiniteCoord
    (w : InfinitePlace K) : IdeleGroup R K →* w.Completionˣ :=
  Units.map <| (Pi.evalMonoidHom _ w).comp
    (MonoidHom.fst (InfiniteAdeleRing K) (FiniteAdeleRing R K))

@[simp]
theorem IsDedekindDomain.HeightOneSpectrum.coe_ideleFiniteCoord
    (v : HeightOneSpectrum R) (x : IdeleGroup R K) :
    (v.ideleFiniteCoord x : v.adicCompletion K) = (x : AdeleRing R K).2 v :=
  (rfl)

@[simp]
theorem NumberField.InfinitePlace.coe_ideleInfiniteCoord
    (w : InfinitePlace K) (x : IdeleGroup R K) :
    (w.ideleInfiniteCoord x : w.Completion) = (x : AdeleRing R K).1 w :=
  (rfl)

/-- The finite coordinate of a principal idele is the image of the global element. -/
@[simp]
theorem IsDedekindDomain.HeightOneSpectrum.ideleFiniteCoord_unitEmbedding
    (v : HeightOneSpectrum R) (x : Kˣ) :
    v.ideleFiniteCoord (IdeleGroup.unitEmbedding R K x) =
      Units.map (algebraMap K (v.adicCompletion K)).toMonoidHom x :=
  Units.ext (rfl)

/-- The infinite coordinate of a principal idele is the image of the global element. -/
@[simp]
theorem NumberField.InfinitePlace.ideleInfiniteCoord_unitEmbedding
    (w : InfinitePlace K) (x : Kˣ) :
    w.ideleInfiniteCoord (IdeleGroup.unitEmbedding R K x) =
      Units.map (algebraMap K w.Completion).toMonoidHom x :=
  Units.ext (rfl)

/-- At its own place, the finite coordinate of an idele concentrated at a finite place `v` is the
given unit of `K_v`. -/
@[simp]
theorem IsDedekindDomain.HeightOneSpectrum.ideleFiniteCoord_ofAdicCompletion_self
    (v : HeightOneSpectrum R)
    (u : (v.adicCompletion K)ˣ) :
    v.ideleFiniteCoord (IdeleGroup.ofAdicCompletion R K v u) = u :=
  Units.ext <| by
    classical
    exact (FiniteAdeleRing.ofAdicCompletion_apply_coe K v u v).trans
      (Pi.mulSingle_eq_same _ _)

/-- Away from its own place, the finite coordinates of an idele concentrated at a finite place are
trivial. -/
@[simp]
theorem IsDedekindDomain.HeightOneSpectrum.ideleFiniteCoord_ofAdicCompletion_of_ne
    (v' : HeightOneSpectrum R) {v : HeightOneSpectrum R} (h : v' ≠ v)
    (u : (v.adicCompletion K)ˣ) :
    v'.ideleFiniteCoord (IdeleGroup.ofAdicCompletion R K v u) = 1 :=
  Units.ext <| by
    classical
    exact (FiniteAdeleRing.ofAdicCompletion_apply_coe K v u v').trans
      (Pi.mulSingle_eq_of_ne h _)

/-- The finite coordinates of a product of ideles, one concentrated at each place of a finite set
`S` of finite places: the prescribed unit at a place of `S`, and `1` elsewhere. -/
theorem IsDedekindDomain.HeightOneSpectrum.ideleFiniteCoord_prod_ofAdicCompletion
    [DecidableEq (HeightOneSpectrum R)] (v' : HeightOneSpectrum R)
    (S : Finset (HeightOneSpectrum R)) (u : ∀ v : HeightOneSpectrum R, (v.adicCompletion K)ˣ) :
    v'.ideleFiniteCoord (∏ v ∈ S, IdeleGroup.ofAdicCompletion R K v (u v)) =
      if v' ∈ S then u v' else 1 := by
  rw [map_prod]
  split_ifs with hv'
  · rw [Finset.prod_eq_single_of_mem v' hv' fun v _ hv ↦
      v'.ideleFiniteCoord_ofAdicCompletion_of_ne (Ne.symm hv) (u v)]
    exact v'.ideleFiniteCoord_ofAdicCompletion_self (u v')
  · exact Finset.prod_eq_one fun v hv ↦
      v'.ideleFiniteCoord_ofAdicCompletion_of_ne (ne_of_mem_of_not_mem hv hv').symm (u v)

/-- The infinite coordinates of an idele concentrated at a finite place are trivial. -/
@[simp]
theorem NumberField.InfinitePlace.ideleInfiniteCoord_ofAdicCompletion
    (w : InfinitePlace K) (v : HeightOneSpectrum R)
    (u : (v.adicCompletion K)ˣ) :
    w.ideleInfiniteCoord (IdeleGroup.ofAdicCompletion R K v u) = 1 :=
  Units.ext (rfl)

/-- At its own place, the infinite coordinate of an idele concentrated at an infinite place `w`
is the given unit of `K_w`. -/
@[simp]
theorem NumberField.InfinitePlace.ideleInfiniteCoord_ofCompletion_self
    (w : InfinitePlace K) (u : w.Completionˣ) :
    w.ideleInfiniteCoord (IdeleGroup.ofCompletion R K w u) = u :=
  Units.ext <| by
    classical
    exact (InfiniteAdeleRing.ofCompletion_apply w u w).trans (Pi.mulSingle_eq_same _ _)

/-- Away from its own place, the infinite coordinates of an idele concentrated at an infinite
place are trivial. -/
@[simp]
theorem NumberField.InfinitePlace.ideleInfiniteCoord_ofCompletion_of_ne
    (w' : InfinitePlace K) {w : InfinitePlace K} (h : w' ≠ w)
    (u : w.Completionˣ) :
    w'.ideleInfiniteCoord (IdeleGroup.ofCompletion R K w u) = 1 :=
  Units.ext <| by
    classical
    exact (InfiniteAdeleRing.ofCompletion_apply w u w').trans
      (Pi.mulSingle_eq_of_ne h _)

/-- The infinite coordinates of an idele with trivial infinite components are trivial. -/
@[simp]
theorem NumberField.InfinitePlace.ideleInfiniteCoord_ofFiniteIdele
    (w : InfinitePlace K) (a : (FiniteAdeleRing R K)ˣ) :
    w.ideleInfiniteCoord (IdeleGroup.ofFiniteIdele R K a) = 1 :=
  Units.ext <| by
    rw [coe_ideleInfiniteCoord, IdeleGroup.coe_ofFiniteIdele]
    rfl

/-- The finite coordinate of an idele built from a finite idele is its original coordinate. -/
@[simp]
theorem IsDedekindDomain.HeightOneSpectrum.ideleFiniteCoord_ofFiniteIdele
    (v : HeightOneSpectrum R) (a : (FiniteAdeleRing R K)ˣ) :
    v.ideleFiniteCoord (IdeleGroup.ofFiniteIdele R K a) =
      Units.map (RestrictedProduct.evalMonoidHom _ v) a :=
  Units.ext <| by
    rw [coe_ideleFiniteCoord, IdeleGroup.coe_ofFiniteIdele]
    exact (Units.coe_map (RestrictedProduct.evalMonoidHom _ v) a).symm

/-- The finite coordinates of an idele concentrated at an infinite place are trivial. -/
@[simp]
theorem IsDedekindDomain.HeightOneSpectrum.ideleFiniteCoord_ofCompletion
    (v : HeightOneSpectrum R) (w : InfinitePlace K)
    (u : w.Completionˣ) :
    v.ideleFiniteCoord (IdeleGroup.ofCompletion R K w u) = 1 :=
  Units.ext (rfl)

end Coordinates

namespace TauCeti.GlobalNumberFields

variable [NumberField K]

/-- The finite coordinates of an idele are units of the valuation ring, that is, have norm `1`,
at all but finitely many places. -/
theorem eventually_norm_ideleFiniteCoord_eq_one (x : IdeleGroup (𝓞 K) K) :
    ∀ᶠ v : HeightOneSpectrum (𝓞 K) in Filter.cofinite,
      ‖(v.ideleFiniteCoord x : v.adicCompletion K)‖ = 1 := by
  have hx : IsUnit (x : AdeleRing (𝓞 K) K).2 :=
    x.isUnit.map (RingHom.snd (InfiniteAdeleRing K) (FiniteAdeleRing (𝓞 K) K))
  filter_upwards [(FiniteAdeleRing.isUnit_iff.mp hx).2] with v hv
  rw [HeightOneSpectrum.coe_ideleFiniteCoord, FinitePlace.norm_def, hv]
  simp

/-- The norms of the finite coordinates of an idele have finite multiplicative support. -/
theorem hasFiniteMulSupport_norm_ideleFiniteCoord (x : IdeleGroup (𝓞 K) K) :
    Function.HasFiniteMulSupport fun v : HeightOneSpectrum (𝓞 K) ↦
      ‖(v.ideleFiniteCoord x : v.adicCompletion K)‖ :=
  Filter.eventually_cofinite.mp (eventually_norm_ideleFiniteCoord_eq_one x)

/-! ### The idele norm -/

/-- The product of the normalized local absolute values of the coordinates of an idele, as a real
number; `coe_ideleNorm` states this formula for the bundled `ideleNorm`. -/
private def ideleNormAux (x : IdeleGroup (𝓞 K) K) : ℝ :=
  (∏ w, infiniteCompletionNormalizedAbsValue w (w.ideleInfiniteCoord x)) *
    ∏ᶠ v : HeightOneSpectrum (𝓞 K), ‖(v.ideleFiniteCoord x : v.adicCompletion K)‖

private lemma ideleNormAux_nonneg (x : IdeleGroup (𝓞 K) K) : 0 ≤ ideleNormAux x :=
  mul_nonneg (Finset.prod_nonneg fun w _ ↦ by simp [infiniteCompletionNormalizedAbsValue_apply])
    (finprod_nonneg fun _ ↦ norm_nonneg _)

private lemma ideleNormAux_mul (x y : IdeleGroup (𝓞 K) K) :
    ideleNormAux (x * y) = ideleNormAux x * ideleNormAux y := by
  simp only [ideleNormAux, map_mul, Units.val_mul, norm_mul, Finset.prod_mul_distrib]
  rw [finprod_mul_distrib (hasFiniteMulSupport_norm_ideleFiniteCoord x)
    (hasFiniteMulSupport_norm_ideleFiniteCoord y)]
  ring

/-- **The idele norm** of a number field: the product over all places of the normalized local
absolute values of the coordinates of an idele, a positive real number.  At a real place the local
factor is the absolute value, at a complex place its square, and at a finite place the norm of the
`v`-adic completion, which is `1` at almost every place. -/
def ideleNorm : IdeleGroup (𝓞 K) K →* ℝ≥0ˣ :=
  MonoidHom.toHomUnits
    { toFun x := (ideleNormAux x).toNNReal
      map_one' := by simp [ideleNormAux]
      map_mul' x y := by rw [ideleNormAux_mul, Real.toNNReal_mul (ideleNormAux_nonneg x)] }

/-- The idele norm is the product of the normalized local absolute values of the coordinates. -/
theorem coe_ideleNorm (x : IdeleGroup (𝓞 K) K) :
    ((ideleNorm x : ℝ≥0) : ℝ) =
      (∏ w, infiniteCompletionNormalizedAbsValue w (w.ideleInfiniteCoord x)) *
        ∏ᶠ v : HeightOneSpectrum (𝓞 K), ‖(v.ideleFiniteCoord x : v.adicCompletion K)‖ :=
  Real.coe_toNNReal _ (ideleNormAux_nonneg x)

/-- **The product formula on ideles**: the idele norm of a principal idele is `1`. -/
@[simp]
theorem ideleNorm_unitEmbedding (x : Kˣ) : ideleNorm (IdeleGroup.unitEmbedding (𝓞 K) K x) = 1 := by
  have hfin (v : HeightOneSpectrum (𝓞 K)) :
      ‖(v.ideleFiniteCoord (IdeleGroup.unitEmbedding (𝓞 K) K x) : v.adicCompletion K)‖ =
        normalizedAbsValue (Sum.inl v) (x : K) := by
    rw [normalizedAbsValue_inl, ← FinitePlace.norm_embedding]
    simp only [HeightOneSpectrum.ideleFiniteCoord_unitEmbedding, Units.coe_map,
      RingHom.toMonoidHom_eq_coe,
      MonoidHom.coe_coe]
    rw [IsDedekindDomain.HeightOneSpectrum.algebraMap_adicCompletion, Function.comp_apply,
      FinitePlace.embedding_apply]
    simp
  ext
  rw [coe_ideleNorm, finprod_congr hfin, finprod_normalizedAbsValue_inl x.ne_zero]
  simp only [InfinitePlace.ideleInfiniteCoord_unitEmbedding, Units.coe_map,
    RingHom.toMonoidHom_eq_coe,
    MonoidHom.coe_coe, infiniteCompletionNormalizedAbsValue_algebraMap,
    InfinitePlace.prod_eq_abs_norm]
  have h0 : |Algebra.norm ℚ (x : K)| ≠ 0 := by simp [Algebra.norm_eq_zero_iff]
  push_cast
  rw [mul_inv_cancel₀ (by exact_mod_cast h0)]

/-- The idele norm is trivial on the principal ideles. -/
theorem principalSubgroup_le_ker_ideleNorm :
    IdeleGroup.principalSubgroup (𝓞 K) K ≤ (ideleNorm (K := K)).ker := by
  rintro _ ⟨x, rfl⟩
  exact ideleNorm_unitEmbedding x

/-- On an idele concentrated at one finite place `v`, the idele norm is the norm of the `v`-adic
coordinate. -/
@[simp]
theorem coe_ideleNorm_ofAdicCompletion (v : HeightOneSpectrum (𝓞 K))
    (u : (v.adicCompletion K)ˣ) :
    ((ideleNorm (IdeleGroup.ofAdicCompletion (𝓞 K) K v u) : ℝ≥0) : ℝ) =
      ‖(u : v.adicCompletion K)‖ := by
  rw [coe_ideleNorm, finprod_eq_single _ v fun v' hv' ↦ by
    simp [v'.ideleFiniteCoord_ofAdicCompletion_of_ne hv']]
  simp

/-- On an idele concentrated at one infinite place `w`, the idele norm is the normalized absolute
value of the `w`-coordinate. -/
@[simp]
theorem coe_ideleNorm_ofCompletion (w : InfinitePlace K) (u : w.Completionˣ) :
    ((ideleNorm (IdeleGroup.ofCompletion (𝓞 K) K w u) : ℝ≥0) : ℝ) =
      infiniteCompletionNormalizedAbsValue w u := by
  rw [coe_ideleNorm, Finset.prod_eq_single w (fun w' _ hw' ↦ by
    simp [w'.ideleInfiniteCoord_ofCompletion_of_ne hw']) (by simp)]
  simp

/-! ### Continuity and surjectivity -/

/-- An idele whose finite coordinates, and those of its inverse, are all integral has finite
coordinates of norm `1`. -/
private lemma norm_ideleFiniteCoord_eq_one_of_forall_mem {u : IdeleGroup (𝓞 K) K}
    (hu : ∀ v : HeightOneSpectrum (𝓞 K),
      (u : AdeleRing (𝓞 K) K).2 v ∈ v.adicCompletionIntegers K)
    (hu' : ∀ v : HeightOneSpectrum (𝓞 K),
      ((u⁻¹ : IdeleGroup (𝓞 K) K) : AdeleRing (𝓞 K) K).2 v ∈ v.adicCompletionIntegers K)
    (v : HeightOneSpectrum (𝓞 K)) :
    ‖(v.ideleFiniteCoord u : v.adicCompletion K)‖ = 1 := by
  have h₁ : ‖(v.ideleFiniteCoord u : v.adicCompletion K)‖ ≤ 1 :=
    Valued.toNormedField.norm_le_one_iff.mpr (hu v)
  have h₂ : ‖(v.ideleFiniteCoord u⁻¹ : v.adicCompletion K)‖ ≤ 1 :=
    Valued.toNormedField.norm_le_one_iff.mpr (hu' v)
  have h : ‖(v.ideleFiniteCoord u : v.adicCompletion K)‖ *
      ‖(v.ideleFiniteCoord u⁻¹ : v.adicCompletion K)‖ = 1 := by
    rw [← norm_mul, ← Units.val_mul, ← map_mul, mul_inv_cancel, map_one, Units.val_one, norm_one]
  nlinarith [norm_nonneg (v.ideleFiniteCoord u : v.adicCompletion K),
    norm_nonneg (v.ideleFiniteCoord u⁻¹ : v.adicCompletion K)]

/-- The idele norm is locally the product of the infinite factors, up to a constant: the ideles
whose finite coordinates are units of the valuation rings form an open neighbourhood of `1` on
which every finite factor is `1`. -/
private lemma continuous_ideleNormAux : Continuous (ideleNormAux (K := K)) := by
  let W : Set (AdeleRing (𝓞 K) K) :=
    {a | ∀ v : HeightOneSpectrum (𝓞 K), a.2 v ∈ v.adicCompletionIntegers K}
  have hW : IsOpen W := (RestrictedProduct.isOpen_forall_mem fun v ↦
    Valued.isOpen_valuationSubring _).preimage continuous_snd
  let U : Set (IdeleGroup (𝓞 K) K) := {u | (u : AdeleRing (𝓞 K) K) ∈ W ∧
    ((u⁻¹ : IdeleGroup (𝓞 K) K) : AdeleRing (𝓞 K) K) ∈ W}
  have hU : IsOpen U :=
    (hW.preimage Units.continuous_val).inter (hW.preimage Units.continuous_coe_inv)
  have hinf : Continuous fun x : IdeleGroup (𝓞 K) K ↦
      ∏ w, infiniteCompletionNormalizedAbsValue w (w.ideleInfiniteCoord x) :=
    continuous_finsetProd _ fun w _ ↦ (continuous_infiniteCompletionNormalizedAbsValue w).comp
      (((continuous_apply w).comp continuous_fst).comp Units.continuous_val)
  have hU_eq (u : IdeleGroup (𝓞 K) K) (hu : u ∈ U) :
      ideleNormAux u = ∏ w, infiniteCompletionNormalizedAbsValue w (w.ideleInfiniteCoord u) := by
    rw [ideleNormAux, finprod_congr (norm_ideleFiniteCoord_eq_one_of_forall_mem hu.1 hu.2),
      finprod_one, mul_one]
  refine continuous_iff_continuousAt.mpr fun x ↦ ?_
  have hmul : Continuous fun y : IdeleGroup (𝓞 K) K ↦ x⁻¹ * y := continuous_const.mul continuous_id
  have hx : ∀ᶠ y in nhds x, x⁻¹ * y ∈ U :=
    hmul.continuousAt.preimage_mem_nhds <|
      hU.mem_nhds <| by
        rw [inv_mul_cancel]
        exact ⟨fun v ↦ (v.adicCompletionIntegers K).one_mem,
          fun v ↦ (v.adicCompletionIntegers K).one_mem⟩
  refine (((continuous_const (y := ideleNormAux x)).mul (hinf.comp hmul)).continuousAt
    (x := x)).congr ?_
  filter_upwards [hx] with y hy
  rw [Pi.mul_apply, Function.comp_apply, ← hU_eq _ hy, ← ideleNormAux_mul, mul_inv_cancel_left]

/-- The idele norm is continuous. -/
theorem continuous_ideleNorm : Continuous (ideleNorm (K := K)) := by
  have h : Continuous fun x : IdeleGroup (𝓞 K) K ↦ (ideleNorm x : ℝ≥0) :=
    continuous_real_toNNReal.comp continuous_ideleNormAux
  exact Units.continuous_iff.mpr ⟨h, (h.comp continuous_inv).congr fun x ↦ by simp⟩

/-- The idele norm is surjective: every positive real number is the idele norm of an idele
concentrated at a single infinite place. -/
theorem ideleNorm_surjective : Function.Surjective (ideleNorm (K := K)) := by
  intro t
  obtain ⟨w⟩ := (inferInstance : Nonempty (InfinitePlace K))
  obtain ⟨x, hx⟩ := exists_infiniteCompletionNormalizedAbsValue_eq w (t : ℝ≥0).coe_nonneg
  have hx0 : x ≠ 0 := by
    rintro rfl
    rw [map_zero] at hx
    exact t.ne_zero (by exact_mod_cast hx.symm)
  refine ⟨IdeleGroup.ofCompletion (𝓞 K) K w (Units.mk0 x hx0), Units.ext <| NNReal.eq ?_⟩
  rw [coe_ideleNorm_ofCompletion, Units.val_mk0, hx]

end TauCeti.GlobalNumberFields
