/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import Mathlib.LinearAlgebra.BilinearForm.Orthogonal
public import Mathlib.LinearAlgebra.Dual.Lemmas
public import Mathlib.LinearAlgebra.QuadraticForm.Prod
public import Mathlib.LinearAlgebra.QuadraticForm.Radical

/-!
# Totally isotropic submodules

A submodule `W` of `M` is *totally isotropic* for a quadratic map `Q` when `Q` vanishes on every
vector of `W`, that is, when the restriction of `Q` to `W` is zero.

## Main definitions

* `QuadraticMap.IsTotallyIsotropic`: a submodule on which a quadratic map vanishes.

## Main results

* `QuadraticMap.isTotallyIsotropic_iff_restrict_eq_zero`: total isotropy is the vanishing of the
  restricted form.
* `QuadraticMap.isTotallyIsotropic_comp_iff`: total isotropy for `Q.comp f` is total isotropy of
  the image under `f`.
* `QuadraticMap.IsTotallyIsotropic.prod`, `QuadraticMap.isTotallyIsotropic_pi_iff`: products and
  finite `pi` sums of totally isotropic submodules are totally isotropic.
* `QuadraticMap.IsTotallyIsotropic.le_orthogonal_polarBilin`,
  `QuadraticMap.IsTotallyIsotropic.two_mul_finrank_le`,
  `QuadraticMap.IsTotallyIsotropic.eq_orthogonal_polarBilin_iff`: a totally isotropic submodule lies
  in its polar orthogonal complement, has dimension at most half the ambient dimension when the
  polar form is nondegenerate, and equals its polar orthogonal complement exactly at half the
  ambient dimension.
* `QuadraticMap.maximal_isTotallyIsotropic_bot_iff`: the zero submodule is maximal totally
  isotropic exactly when the form is anisotropic.
* `QuadraticMap.IsTotallyIsotropic.eq_zero_of_polar_eq_zero`: for a nondegenerate form and
  `W ⊔ W' = ⊤` with `W'` totally isotropic, a vector of `W'` which is polar-orthogonal to `W`
  vanishes.
* `QuadraticMap.IsTotallyIsotropic.finrank_eq_of_codisjoint`: two totally isotropic subspaces
  spanning a nondegenerate quadratic space have the same `finrank` (the dimension when finite,
  and `0` for both otherwise).

The Witt-index comparison for maximal totally isotropic subspaces (Lam I.4.4) is in
`TauCeti.LinearAlgebra.QuadraticForm.Witt.TotallyIsotropic`.
-/

public section

namespace QuadraticMap

section Semiring

variable {R M M' N : Type*} [CommSemiring R] [AddCommMonoid M] [Module R M]
  [AddCommMonoid M'] [Module R M'] [AddCommMonoid N] [Module R N] {Q : QuadraticMap R M N}
  {W W' : Submodule R M}

/-- A submodule `W` is *totally isotropic* for a quadratic map `Q` when `Q` vanishes on every
vector of `W`. -/
def IsTotallyIsotropic (Q : QuadraticMap R M N) (W : Submodule R M) : Prop :=
  ∀ v ∈ W, Q v = 0

/-- Unfolds `QuadraticMap.IsTotallyIsotropic`. -/
theorem isTotallyIsotropic_iff : Q.IsTotallyIsotropic W ↔ ∀ v ∈ W, Q v = 0 := Iff.rfl

/-- A quadratic map vanishes on each vector of a totally isotropic submodule. -/
theorem IsTotallyIsotropic.apply_eq_zero (hW : Q.IsTotallyIsotropic W) {v : M} (hv : v ∈ W) :
    Q v = 0 :=
  hW v hv

/-- A submodule is totally isotropic exactly when the restriction of the form to it is zero. -/
theorem isTotallyIsotropic_iff_restrict_eq_zero : Q.IsTotallyIsotropic W ↔ Q.restrict W = 0 :=
  ⟨fun h ↦ QuadraticMap.ext fun v ↦ h v v.2, fun h v hv ↦ by
    simpa using congr($h ⟨v, hv⟩)⟩

/-- A submodule is totally isotropic for `Q.comp f` exactly when its image under `f` is totally
isotropic for `Q`. -/
theorem isTotallyIsotropic_comp_iff {f : M' →ₗ[R] M} {T : Submodule R M'} :
    (Q.comp f).IsTotallyIsotropic T ↔ Q.IsTotallyIsotropic (T.map f) := by
  simp only [isTotallyIsotropic_iff, Submodule.mem_map, forall_exists_index, and_imp,
    forall_apply_eq_imp_iff₂, comp_apply]

/-- The preimage of a totally isotropic submodule under a linear map `f` is totally isotropic
for `Q.comp f`. -/
theorem IsTotallyIsotropic.comap (hW : Q.IsTotallyIsotropic W) (f : M' →ₗ[R] M) :
    (Q.comp f).IsTotallyIsotropic (W.comap f) :=
  fun _ hv ↦ hW _ hv

/-- A submodule of `U` is totally isotropic for the restriction of `Q` to `U` exactly when it is
totally isotropic for `Q` as a submodule of `M`. -/
theorem isTotallyIsotropic_restrict_iff {U : Submodule R M} {T : Submodule R U} :
    (Q.restrict U).IsTotallyIsotropic T ↔ Q.IsTotallyIsotropic (T.map U.subtype) :=
  isTotallyIsotropic_comp_iff (Q := Q) (f := U.subtype)

/-- The vectors of `U` lying in a totally isotropic submodule `W` form a totally isotropic
submodule for the restriction of `Q` to `U`. -/
theorem IsTotallyIsotropic.restrict (hW : Q.IsTotallyIsotropic W) (U : Submodule R M) :
    (Q.restrict U).IsTotallyIsotropic (W.comap U.subtype) :=
  hW.comap U.subtype

/-- The zero submodule is totally isotropic. -/
@[simp]
theorem isTotallyIsotropic_bot : Q.IsTotallyIsotropic ⊥ := by
  intro v hv
  rw [Submodule.mem_bot] at hv
  rw [hv, map_zero]

/-- A submodule of a totally isotropic submodule is totally isotropic. -/
theorem IsTotallyIsotropic.mono (hW : Q.IsTotallyIsotropic W) (h : W' ≤ W) :
    Q.IsTotallyIsotropic W' :=
  fun v hv ↦ hW v (h hv)

/-- A line is totally isotropic exactly when its spanning vector is isotropic. -/
@[simp]
theorem isTotallyIsotropic_span_singleton_iff {v : M} :
    Q.IsTotallyIsotropic (R ∙ v) ↔ Q v = 0 := by
  refine ⟨fun h ↦ h v (Submodule.mem_span_singleton_self v), fun h u hu ↦ ?_⟩
  obtain ⟨c, rfl⟩ := Submodule.mem_span_singleton.mp hu
  rw [QuadraticMap.map_smul, h, smul_zero]

/-- The zero subspace is a maximal totally isotropic subspace exactly when the form is
anisotropic. -/
theorem maximal_isTotallyIsotropic_bot_iff :
    Maximal Q.IsTotallyIsotropic ⊥ ↔ Q.Anisotropic := by
  refine ⟨fun h v hv ↦ ?_, fun h ↦ ⟨isTotallyIsotropic_bot, fun U hU _ v hv ↦ ?_⟩⟩
  · have hle := h.2 (isTotallyIsotropic_span_singleton_iff.mpr hv) bot_le
    rwa [le_bot_iff, Submodule.span_singleton_eq_bot] at hle
  · rw [Submodule.mem_bot]
    exact h v (hU v hv)

/-- The product of two totally isotropic submodules is totally isotropic for the product quadratic
map. -/
theorem IsTotallyIsotropic.prod {Q' : QuadraticMap R M' N} {T : Submodule R M'}
    (hW : Q.IsTotallyIsotropic W) (hT : Q'.IsTotallyIsotropic T) :
    (Q.prod Q').IsTotallyIsotropic (W.prod T) := by
  rintro ⟨v, w⟩ ⟨hv, hw⟩
  simp [hW v hv, hT w hw]

/-- A product of submodules is totally isotropic for a product of quadratic maps when each factor
is totally isotropic. -/
@[simp]
theorem isTotallyIsotropic_pi_iff {ι : Type*} [Fintype ι] {Mᵢ : ι → Type*}
    [∀ i, AddCommMonoid (Mᵢ i)] [∀ i, Module R (Mᵢ i)]
    {Qᵢ : ∀ i, QuadraticMap R (Mᵢ i) N} {Wᵢ : ∀ i, Submodule R (Mᵢ i)} :
    (QuadraticMap.pi Qᵢ).IsTotallyIsotropic (Submodule.pi Set.univ Wᵢ) ↔
      ∀ i, (Qᵢ i).IsTotallyIsotropic (Wᵢ i) := by
  classical
  refine ⟨fun h i v hv ↦ ?_, fun h x hx ↦ ?_⟩
  · have hsingle := h (Pi.single i v) fun j _ ↦ by
      rcases eq_or_ne j i with rfl | hj
      · simpa using hv
      · simp [Pi.single_eq_of_ne hj]
    rwa [QuadraticMap.pi_apply, Finset.sum_eq_single i
      (fun j _ hj ↦ by rw [Pi.single_eq_of_ne hj, map_zero])
      (fun hi ↦ absurd (Finset.mem_univ i) hi), Pi.single_eq_same] at hsingle
  · rw [QuadraticMap.pi_apply]
    exact Finset.sum_eq_zero fun i _ ↦ h i (x i) (hx i (Set.mem_univ i))

end Semiring

section Group

variable {R M N : Type*} [CommSemiring R] [AddCommGroup M] [Module R M]
  [AddCommGroup N] [Module R N] {Q : QuadraticMap R M N} {W : Submodule R M}

/-- The polar form vanishes on pairs of vectors of a totally isotropic submodule. -/
theorem IsTotallyIsotropic.polar_eq_zero (hW : Q.IsTotallyIsotropic W) {v w : M} (hv : v ∈ W)
    (hw : w ∈ W) : polar Q v w = 0 := by
  rw [polar, hW _ (W.add_mem hv hw), hW v hv, hW w hw, sub_zero, sub_zero]

end Group

section Ring

variable {R M N : Type*} [CommRing R] [AddCommGroup M] [Module R M]
  [AddCommGroup N] [Module R N] {Q : QuadraticMap R M N} {W W' : Submodule R M}

omit [AddCommGroup N] [Module R N] in
/-- A totally isotropic submodule of a scalar-valued quadratic map lies in its polar orthogonal
complement. -/
theorem IsTotallyIsotropic.le_orthogonal_polarBilin {Q : QuadraticForm R M}
    (hW : Q.IsTotallyIsotropic W) :
    W ≤ LinearMap.BilinForm.orthogonal Q.polarBilin W :=
  fun v hv u hu => by simpa only [polarBilin_apply_apply] using hW.polar_eq_zero hu hv

/-- For a nondegenerate `Q`, if `W ⊔ W' = ⊤` with `W'` totally isotropic, a vector of `W'`
which is polar-orthogonal to `W` vanishes: it is then polar-orthogonal to all of `M = W + W'`,
hence lies in the radical. -/
theorem IsTotallyIsotropic.eq_zero_of_polar_eq_zero (hW' : Q.IsTotallyIsotropic W')
    (hQ : Q.Nondegenerate) (hWW' : Codisjoint W W') {y : M} (hy : y ∈ W')
    (hyW : ∀ x ∈ W, polar Q x y = 0) : y = 0 := by
  have hpolar (z : M) : polar Q y z = 0 := by
    obtain ⟨x, hx, z', hz', rfl⟩ := Submodule.mem_sup.mp (hWW'.eq_top ▸
      Submodule.mem_top : z ∈ W ⊔ W')
    rw [polar_add_right, hW'.polar_eq_zero hy hz', polar_comm, hyW x hx, add_zero]
  have hrad : y ∈ Q.radical := ⟨hW'.apply_eq_zero hy, LinearMap.ext hpolar⟩
  simpa [hQ.radical_eq_bot] using hrad

/-- For a nondegenerate `Q` and `W ⊔ W' = ⊤` with `W'` totally isotropic, the polar pairing of
`W'` with `W` is injective in the `W'` variable. -/
theorem IsTotallyIsotropic.polarBilin_compl₁₂_flip_injective (hW' : Q.IsTotallyIsotropic W')
    (hQ : Q.Nondegenerate) (hWW' : Codisjoint W W') :
    Function.Injective ((polarBilin Q).compl₁₂ W.subtype W'.subtype).flip := by
  refine (injective_iff_map_eq_zero _).mpr fun y hy => Subtype.ext ?_
  refine hW'.eq_zero_of_polar_eq_zero hQ hWW' y.2 fun x hx => ?_
  simpa using LinearMap.congr_fun hy ⟨x, hx⟩

end Ring

section Field

variable {K V : Type*} [Field K] [AddCommGroup V] [Module K V]
  {Q : QuadraticForm K V} {W W' : Submodule K V}

/-- If `W` is finite-dimensional and `W ⊔ W' = ⊤` with `W'` totally isotropic in a nondegenerate
space, then `W'` is finite-dimensional: the polar pairing embeds `W'` into the dual of `W`. -/
theorem IsTotallyIsotropic.finiteDimensional_of_codisjoint (hW' : Q.IsTotallyIsotropic W')
    (hQ : Q.Nondegenerate) (hWW' : Codisjoint W W') [FiniteDimensional K W] :
    FiniteDimensional K W' :=
  Module.Finite.of_injective _ (hW'.polarBilin_compl₁₂_flip_injective hQ hWW')

/-- If `W` is finite-dimensional and `W ⊔ W' = ⊤` with `W'` totally isotropic in a nondegenerate
space, then `W'` has dimension at most that of `W`: the polar pairing embeds `W'` into the dual
of `W`. -/
theorem IsTotallyIsotropic.finrank_le_of_codisjoint (hW' : Q.IsTotallyIsotropic W')
    (hQ : Q.Nondegenerate) (hWW' : Codisjoint W W') [FiniteDimensional K W] :
    Module.finrank K W' ≤ Module.finrank K W := by
  simpa [Subspace.dual_finrank_eq] using
    LinearMap.finrank_le_finrank_of_injective (hW'.polarBilin_compl₁₂_flip_injective hQ hWW')

/-- Two totally isotropic subspaces spanning a nondegenerate quadratic space have the same
`Module.finrank`: the polar pairing embeds each into the dual of the other.  This is the equality
of their dimensions when they are finite-dimensional, and otherwise both `finrank`s are `0`. -/
theorem IsTotallyIsotropic.finrank_eq_of_codisjoint (hW : Q.IsTotallyIsotropic W)
    (hW' : Q.IsTotallyIsotropic W') (hQ : Q.Nondegenerate) (hWW' : Codisjoint W W') :
    Module.finrank K W' = Module.finrank K W := by
  by_cases hfW : FiniteDimensional K W
  · have := hW'.finiteDimensional_of_codisjoint hQ hWW'
    exact le_antisymm (hW'.finrank_le_of_codisjoint hQ hWW')
      (hW.finrank_le_of_codisjoint hQ hWW'.symm)
  · by_cases hfW' : FiniteDimensional K W'
    · exact absurd (hW.finiteDimensional_of_codisjoint hQ hWW'.symm) hfW
    · rw [Module.finrank_of_not_finite hfW, Module.finrank_of_not_finite hfW']

/-- In a finite-dimensional space whose polar bilinear form is nondegenerate, a totally isotropic
subspace has dimension at most half the ambient dimension. -/
theorem IsTotallyIsotropic.two_mul_finrank_le [FiniteDimensional K V]
    (hW : Q.IsTotallyIsotropic W) (hQ : Q.polarBilin.Nondegenerate) :
    2 * Module.finrank K W ≤ Module.finrank K V := by
  have horth := LinearMap.BilinForm.finrank_orthogonal hQ W
  have hmono := Submodule.finrank_mono hW.le_orthogonal_polarBilin
  have hle := Submodule.finrank_le W
  omega

/-- In a finite-dimensional space whose polar bilinear form is nondegenerate, a totally isotropic
subspace equals its polar orthogonal complement if and only if its dimension is half the ambient
dimension. -/
theorem IsTotallyIsotropic.eq_orthogonal_polarBilin_iff [FiniteDimensional K V]
    (hW : Q.IsTotallyIsotropic W) (hQ : Q.polarBilin.Nondegenerate) :
    W = LinearMap.BilinForm.orthogonal Q.polarBilin W ↔
      2 * Module.finrank K W = Module.finrank K V := by
  have horth := LinearMap.BilinForm.finrank_orthogonal hQ W
  have hle := Submodule.finrank_le W
  refine ⟨fun h => ?_, fun h => Submodule.eq_of_le_of_finrank_eq hW.le_orthogonal_polarBilin ?_⟩
  · rw [← h] at horth
    omega
  · omega

end Field

end QuadraticMap
