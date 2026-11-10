/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import Mathlib.LinearAlgebra.Eigenspace.Basic
public import Mathlib.LinearAlgebra.Projection
public import TauCeti.LinearAlgebra.CliffordAlgebra.VolumeElement.Complex
public import TauCeti.RingTheory.Idempotents.SquareRootOne
-- Private: the following are used only inside proofs: the dimension `2 ^ (n / 2)` of a spinor
-- module, Clifford functoriality, the eigenspace splitting, anticommutation and transport lemmas
-- for endomorphisms, the Morita evaluation of eigenspaces, and the square of a volume element.
import TauCeti.LinearAlgebra.CliffordAlgebra.Dimension
import TauCeti.LinearAlgebra.CliffordAlgebra.Functoriality
import TauCeti.LinearAlgebra.Eigenspace.Anticommute
import TauCeti.LinearAlgebra.Eigenspace.Separation
import TauCeti.LinearAlgebra.Eigenspace.Transport
import TauCeti.LinearAlgebra.CliffordAlgebra.VolumeElement.Basic
import TauCeti.RingTheory.Morita.Eigenspace

/-!
# The chirality decomposition of a complex Clifford module

Let `V` be an oriented real inner product space of dimension `n`, `Q v = -‖v‖²`, and let `E` be
an arbitrary module over the complexified Clifford algebra `Cℓ = CliffordAlgebra (Q.baseChange ℂ)`.
The normalized complex volume element `Γ` (`CliffordAlgebra.complexVolume`) squares to `1`, so `E`
is the direct sum of its eigenspaces

`E⁺ = {ψ | Γ ψ = ψ}`,  `E⁻ = {ψ | Γ ψ = -ψ}`,

with the projections onto them given by the action of the idempotents `½ (1 ± Γ)`
(`TauCeti.halfOneAdd`). Nothing is assumed of `E`: it need not be finite-dimensional, irreducible
or Hermitian.

In even dimension `Γ` commutes with even elements and anticommutes with odd ones, so even elements
preserve `E⁺` and `E⁻` while odd elements, in particular all vectors, exchange them. For a unit
vector `v` the operator `c(v)` squares to `-1`, so it identifies the two eigenspaces and they have
the same dimension as soon as `n > 0`. In odd dimension `Γ` is central, so `E⁺` and `E⁻` are
preserved by the whole Clifford algebra: they are the two multiplicity pieces of `E` for the two
central factors labelled by `Γ = ±1`.

Finally, suppose `n` is positive, and let `S` be a spinor module, a `Cℓ`-module on which `Cℓ` acts
as the whole of `End_ℂ S`, as for the Fock module of an even-dimensional space
(`TauCeti.SpinPolarizationData.cliffordEquivEnd`). Then `n` is even, `S` is finite-dimensional and
`dim S = 2 ^ (n / 2)` (`CliffordAlgebra.finrank_eq_two_pow_of_bijective_lsmul`), its half-spin
spaces `S⁺` and `S⁻` both have dimension `2 ^ (n / 2 - 1)`, and by Morita evaluation
(`TauCeti.eigenspaceTensorEquivOfBijective`) every module satisfies

`E⁺ ≃ S⁺ ⊗ Hom_Cℓ(S, E)`,  `E⁻ ≃ S⁻ ⊗ Hom_Cℓ(S, E)`,

so that `dim E^± = 2 ^ (n / 2 - 1) · dim Hom_Cℓ(S, E)`.

The decomposition is natural: since `Γ` is carried to `Γ` by orientation-preserving isometries of
the quadratic forms that also preserve the norms (`CliffordAlgebra.map_complexVolume`), a map of
Clifford modules intertwining the vectors along such an isometry maps `E^±` into the corresponding
eigenspace of the target, and an equivalence restricts to equivalences of the half-spinors. An
orientation-reversing isometry exchanges the labels.

## Main results

* `CliffordAlgebra.isCompl_eigenspace_complexVolume`: `E = E⁺ ⊕ E⁻`.
* `CliffordAlgebra.projection_eigenspace_complexVolume_apply` and
  `CliffordAlgebra.projection_eigenspace_complexVolume_neg_one_apply`: the projections onto `E⁺`
  and `E⁻` are `½ (1 + Γ)` and `½ (1 - Γ)`.
* `CliffordAlgebra.smul_mem_eigenspace_complexVolume_of_mem_even`: in any dimension, even
  elements preserve the eigenspaces.
* `CliffordAlgebra.smul_mem_eigenspace_complexVolume_neg_of_mem_odd` and
  `CliffordAlgebra.ι_smul_mem_eigenspace_complexVolume_neg`: in even dimension, odd elements and
  vectors exchange the eigenspaces.
* `CliffordAlgebra.smul_mem_eigenspace_complexVolume_of_odd`: in odd dimension, the whole
  Clifford algebra preserves the eigenspaces.
* `CliffordAlgebra.comp_lsmul_complexVolume_eq_lsmul_complexVolume_comp`,
  `CliffordAlgebra.apply_mem_eigenspace_complexVolume` and
  `CliffordAlgebra.map_eigenspace_complexVolume`: a map of Clifford modules intertwining the
  vectors along an orientation-preserving isometry of the quadratic forms that also preserves the
  norms intertwines `Γ`, so it maps each eigenspace into, and for an equivalence onto, the
  corresponding eigenspace.
* `CliffordAlgebra.finrank_eigenspace_complexVolume_neg`: in even positive dimension,
  `dim E⁻ = dim E⁺`.
* `CliffordAlgebra.finrank_eigenspace_complexVolume_of_bijective_lsmul`: in even positive
  dimension, the half-spin spaces of a spinor module have dimension `2 ^ (n / 2 - 1)`.
* `CliffordAlgebra.finrank_eigenspace_complexVolume_eq_mul_finrank_linearMap`: in positive
  dimension, given a spinor module, `dim E^± = 2 ^ (n / 2 - 1) · dim Hom_Cℓ(S, E)`.

## References

* H. B. Lawson and M.-L. Michelsohn, *Spin Geometry* (1989), Chapter I, §5.
* L. Nicolaescu, *Lectures on the Geometry of Manifolds*, the chapter on Clifford modules.
-/

public section

noncomputable section

open Module Module.End TauCeti
open scoped TensorProduct

namespace CliffordAlgebra

variable {V : Type*} [NormedAddCommGroup V] [InnerProductSpace ℝ V] [FiniteDimensional ℝ V]
  {n : ℕ} [Fact (finrank ℝ V = n)] {Q : QuadraticForm ℝ V} (o : Orientation ℝ V (Fin n))
variable {E : Type*} [AddCommGroup E] [Module ℂ E] [Module (CliffordAlgebra (Q.baseChange ℂ)) E]
  [IsScalarTower ℂ (CliffordAlgebra (Q.baseChange ℂ)) E]

/-! ### Clifford multiplication and the eigenspaces of `Γ` -/

/-- In even dimension an odd Clifford element maps the `μ`-eigenspace of `Γ` into the
`-μ`-eigenspace. -/
theorem smul_mem_eigenspace_complexVolume_neg_of_mem_odd (hn : Even n)
    {x : CliffordAlgebra (Q.baseChange ℂ)} (hx : x ∈ evenOdd (Q.baseChange ℂ) 1) {μ : ℂ} {ψ : E}
    (hψ : ψ ∈ (Algebra.lsmul ℂ ℂ E (complexVolume Q o)).eigenspace μ) :
    x • ψ ∈ (Algebra.lsmul ℂ ℂ E (complexVolume Q o)).eigenspace (-μ) := by
  simp only [mem_eigenspace_iff, Algebra.lsmul_coe] at hψ ⊢
  rw [← mul_smul, complexVolume_mul_of_mem_odd o hn hx, neg_smul, mul_smul, hψ, smul_comm,
    neg_smul]

/-- **Vectors exchange the half-spinors**: in even dimension Clifford multiplication by a vector
maps the `μ`-eigenspace of `Γ` into the `-μ`-eigenspace. -/
theorem ι_smul_mem_eigenspace_complexVolume_neg (hn : Even n) (w : ℂ ⊗[ℝ] V) {μ : ℂ} {ψ : E}
    (hψ : ψ ∈ (Algebra.lsmul ℂ ℂ E (complexVolume Q o)).eigenspace μ) :
    ι (Q.baseChange ℂ) w • ψ ∈ (Algebra.lsmul ℂ ℂ E (complexVolume Q o)).eigenspace (-μ) :=
  smul_mem_eigenspace_complexVolume_neg_of_mem_odd o hn (ι_mem_evenOdd_one _ w) hψ

/-- In odd dimension `Γ` is central, so every Clifford element preserves each eigenspace of `Γ`. -/
theorem smul_mem_eigenspace_complexVolume_of_odd (hn : Odd n)
    (x : CliffordAlgebra (Q.baseChange ℂ)) {μ : ℂ} {ψ : E}
    (hψ : ψ ∈ (Algebra.lsmul ℂ ℂ E (complexVolume Q o)).eigenspace μ) :
    x • ψ ∈ (Algebra.lsmul ℂ ℂ E (complexVolume Q o)).eigenspace μ := by
  simp only [mem_eigenspace_iff, Algebra.lsmul_coe] at hψ ⊢
  rw [← mul_smul, ← Subalgebra.mem_center_iff.1 (complexVolume_mem_center o hn) x, mul_smul, hψ,
    smul_comm]

/-- An even Clifford element preserves each eigenspace of `Γ`, in any dimension, because `Γ`
commutes with even elements. -/
theorem smul_mem_eigenspace_complexVolume_of_mem_even
    {x : CliffordAlgebra (Q.baseChange ℂ)} (hx : x ∈ evenOdd (Q.baseChange ℂ) 0) {μ : ℂ} {ψ : E}
    (hψ : ψ ∈ (Algebra.lsmul ℂ ℂ E (complexVolume Q o)).eigenspace μ) :
    x • ψ ∈ (Algebra.lsmul ℂ ℂ E (complexVolume Q o)).eigenspace μ := by
  simp only [mem_eigenspace_iff, Algebra.lsmul_coe] at hψ ⊢
  rw [← mul_smul, (commute_complexVolume_of_mem_even o hx).eq, mul_smul, hψ, smul_comm]

/-! ### Naturality under isometries -/

section Naturality

variable {V' : Type*} [NormedAddCommGroup V'] [InnerProductSpace ℝ V'] [FiniteDimensional ℝ V']
  [Fact (finrank ℝ V' = n)] {Q' : QuadraticForm ℝ V'} {o' : Orientation ℝ V' (Fin n)}
  {F : Type*} [AddCommGroup F] [Module ℂ F] [Module (CliffordAlgebra (Q'.baseChange ℂ)) F]
  [IsScalarTower ℂ (CliffordAlgebra (Q'.baseChange ℂ)) F]
  {e : Q.IsometryEquiv Q'} {U : E →ₗ[ℂ] F}

variable {o}

/-- **Naturality of the chirality action**: a complex-linear map `U` of Clifford modules that
intertwines the real vectors along an isometric equivalence `e` of the quadratic forms,
`U (c(v) ψ) = c(e v) (U ψ)`, where `e` also preserves the norms and carries `o` to `o'`, intertwines
`Γ` for `o` with `Γ` for `o'`. -/
theorem comp_lsmul_complexVolume_eq_lsmul_complexVolume_comp (he : ∀ v, ‖e v‖ = ‖v‖)
    (ho : o.map (Fin n) e.toLinearEquiv = o')
    (hU : ∀ (v : V) (ψ : E),
      U (ι (Q.baseChange ℂ) (1 ⊗ₜ v) • ψ) = ι (Q'.baseChange ℂ) (1 ⊗ₜ e v) • U ψ) :
    U ∘ₗ Algebra.lsmul ℂ ℂ E (complexVolume Q o) =
      Algebra.lsmul ℂ ℂ F (complexVolume Q' o') ∘ₗ U := by
  -- Let the real Clifford algebras act through `ofBaseChangeAux`, so that `U` intertwines the
  -- real volume elements; `Γ` is a scalar multiple of the image of the real volume element.
  have h := comp_eq_map_comp_of_forall_ι
    (ρ₁ := ((Algebra.lsmul ℂ ℂ E).restrictScalars ℝ).comp (ofBaseChangeAux ℂ Q))
    (ρ₂ := ((Algebra.lsmul ℂ ℂ F).restrictScalars ℝ).comp (ofBaseChangeAux ℂ Q'))
    (f := e.toIsometry) (fun v ↦ LinearMap.ext fun ψ ↦ by simpa using hU v ψ) (volumeElement Q o)
  rw [map_volumeElement o e he, ho] at h
  rw [complexVolume_def, complexVolume_def, map_smul, map_smul, LinearMap.comp_smul,
    LinearMap.smul_comp]
  exact congrArg (Complex.I ^ ((n + 1) / 2) • ·) h

/-- An intertwiner as in `CliffordAlgebra.comp_lsmul_complexVolume_eq_lsmul_complexVolume_comp`
maps each eigenspace of `Γ` for `o` into the eigenspace of `Γ` for `o'` with the same eigenvalue.
For an orientation-reversing isometry, take `o' = -o''`: the `μ`-eigenspace of `Γ` for `o'` is the
`-μ`-eigenspace of `Γ` for `o''`, by `CliffordAlgebra.complexVolume_neg_orientation`. -/
theorem apply_mem_eigenspace_complexVolume (he : ∀ v, ‖e v‖ = ‖v‖)
    (ho : o.map (Fin n) e.toLinearEquiv = o')
    (hU : ∀ (v : V) (ψ : E),
      U (ι (Q.baseChange ℂ) (1 ⊗ₜ v) • ψ) = ι (Q'.baseChange ℂ) (1 ⊗ₜ e v) • U ψ)
    {μ : ℂ} {ψ : E} (hψ : ψ ∈ (Algebra.lsmul ℂ ℂ E (complexVolume Q o)).eigenspace μ) :
    U ψ ∈ (Algebra.lsmul ℂ ℂ F (complexVolume Q' o')).eigenspace μ :=
  mapsTo_genEigenspace_of_comp U
    (comp_lsmul_complexVolume_eq_lsmul_complexVolume_comp he ho hU).symm μ 1 hψ

/-- An equivalence of Clifford modules that intertwines the real vectors along an isometric
equivalence `e` as in `CliffordAlgebra.comp_lsmul_complexVolume_eq_lsmul_complexVolume_comp`
carries each eigenspace of `Γ` for `o` onto the eigenspace of `Γ` for `o'` with the same
eigenvalue. For `Q v = -‖v‖²`, `Q' v = -‖v‖²`, even `n` and `μ = ±1` these are the half-spinors,
which are therefore identified by `LinearEquiv.ofSubmodules`. -/
theorem map_eigenspace_complexVolume (he : ∀ v, ‖e v‖ = ‖v‖)
    (ho : o.map (Fin n) e.toLinearEquiv = o') {U : E ≃ₗ[ℂ] F}
    (hU : ∀ (v : V) (ψ : E),
      U (ι (Q.baseChange ℂ) (1 ⊗ₜ v) • ψ) = ι (Q'.baseChange ℂ) (1 ⊗ₜ e v) • U ψ) (μ : ℂ) :
    ((Algebra.lsmul ℂ ℂ E (complexVolume Q o)).eigenspace μ).map U.toLinearMap =
      (Algebra.lsmul ℂ ℂ F (complexVolume Q' o')).eigenspace μ := by
  have h := comp_lsmul_complexVolume_eq_lsmul_complexVolume_comp he ho hU
  rw [eigenspace_eq_comap_of_intertwine (e := U) (g := Algebra.lsmul ℂ ℂ F (complexVolume Q' o'))
    (LinearMap.congr_fun h) μ]
  exact Submodule.map_comap_eq_of_surjective U.surjective _

end Naturality

/-! ### The decomposition `E = E⁺ ⊕ E⁻` -/

section Form

variable (hQ : ∀ v, Q v = -‖v‖ ^ 2)
include hQ

/-- **The chirality decomposition**: every module over the complexified Clifford algebra is the
direct sum of the `1`- and `-1`-eigenspaces of `Γ`. -/
theorem isCompl_eigenspace_complexVolume :
    IsCompl ((Algebra.lsmul ℂ ℂ E (complexVolume Q o)).eigenspace 1)
      ((Algebra.lsmul ℂ ℂ E (complexVolume Q o)).eigenspace (-1)) :=
  isCompl_eigenspace_one_neg_one two_ne_zero.isUnit (lsmul_complexVolume_involutive o hQ)

/-- `½ (1 + Γ)` maps every vector into the `1`-eigenspace of `Γ`. -/
theorem halfOneAdd_smul_mem_eigenspace_complexVolume (ψ : E) :
    halfOneAdd ℂ (complexVolume Q o) • ψ ∈
      (Algebra.lsmul ℂ ℂ E (complexVolume Q o)).eigenspace 1 := by
  simp only [mem_eigenspace_iff, Algebra.lsmul_coe]
  rw [← mul_smul, mul_halfOneAdd ℂ (complexVolume_mul_self o hQ), one_smul]

/-- `½ (1 - Γ)` maps every vector into the `-1`-eigenspace of `Γ`. -/
theorem halfOneAdd_neg_smul_mem_eigenspace_complexVolume (ψ : E) :
    halfOneAdd ℂ (-complexVolume Q o) • ψ ∈
      (Algebra.lsmul ℂ ℂ E (complexVolume Q o)).eigenspace (-1) := by
  simp only [mem_eigenspace_iff, Algebra.lsmul_coe]
  rw [← mul_smul, mul_halfOneAdd_neg ℂ (complexVolume_mul_self o hQ), neg_smul, neg_one_smul]

/-- **The projection onto the `1`-eigenspace** of `Γ`, along the `-1`-eigenspace, is the action
of `½ (1 + Γ)`. -/
theorem projection_eigenspace_complexVolume_apply (ψ : E) :
    Submodule.projection _ _ (isCompl_eigenspace_complexVolume (Q := Q) (E := E) o hQ) ψ =
      halfOneAdd ℂ (complexVolume Q o) • ψ := by
  conv_lhs => rw [← halfOneAdd_smul_add_halfOneAdd_neg_smul ℂ (complexVolume Q o) ψ]
  rw [map_add, Submodule.projection_apply_of_mem_left _
      (halfOneAdd_smul_mem_eigenspace_complexVolume o hQ ψ),
    Submodule.projection_apply_of_mem_right _
      (halfOneAdd_neg_smul_mem_eigenspace_complexVolume o hQ ψ), add_zero]

/-- **The projection onto the `-1`-eigenspace** of `Γ`, along the `1`-eigenspace, is the action
of `½ (1 - Γ)`. -/
theorem projection_eigenspace_complexVolume_neg_one_apply (ψ : E) :
    Submodule.projection _ _ (isCompl_eigenspace_complexVolume (Q := Q) (E := E) o hQ).symm ψ =
      halfOneAdd ℂ (-complexVolume Q o) • ψ := by
  conv_lhs => rw [← halfOneAdd_smul_add_halfOneAdd_neg_smul ℂ (complexVolume Q o) ψ]
  rw [map_add, Submodule.projection_apply_of_mem_right _
      (halfOneAdd_smul_mem_eigenspace_complexVolume o hQ ψ),
    Submodule.projection_apply_of_mem_left _
      (halfOneAdd_neg_smul_mem_eigenspace_complexVolume o hQ ψ), zero_add]

omit hQ in
/-- **The half-spinors have equal dimension**: in even positive dimension, Clifford
multiplication by a vector of nonzero norm identifies the `μ`- and `-μ`-eigenspaces of `Γ`; if
`Q = 0` then `Γ² = 0` and both eigenspaces vanish unless `μ = 0`. -/
theorem finrank_eigenspace_complexVolume_neg (hn : Even n) (hn0 : n ≠ 0) (μ : ℂ) :
    finrank ℂ ((Algebra.lsmul ℂ ℂ E (complexVolume Q o)).eigenspace (-μ)) =
      finrank ℂ ((Algebra.lsmul ℂ ℂ E (complexVolume Q o)).eigenspace μ) := by
  have : NeZero n := ⟨hn0⟩
  by_cases hQ0 : ∀ v, Q v = 0
  · -- `Q = 0`: `Γ² = 0`, so the eigenspaces for nonzero eigenvalues are trivial.
    have hQ' : Q = 0 := QuadraticMap.ext hQ0
    have hsq : complexVolume Q o * complexVolume Q o = 0 := by
      let b := ((stdOrthonormalBasis ℝ V).reindex
        (finCongr (Fact.out : finrank ℝ V = n))).adjustToOrientation o
      have hb : b.toBasis.orientation = o := OrthonormalBasis.orientation_adjustToOrientation _ o
      have hQb : (QuadraticMap.associated Q).IsOrthoᵢ b.toBasis := by
        intro i j _
        simp [hQ', Function.onFun]
      have hl : ((List.finRange n).map b).Pairwise Q.IsOrtho :=
        List.Pairwise.imp (R := fun _ _ => True) (fun _ => by simp [hQ', QuadraticMap.IsOrtho])
          (List.pairwise_of_forall (fun _ _ => trivial))
      have hprod : (((List.finRange n).map b).map Q).prod = 0 := by
        exact List.prod_eq_zero (List.mem_map.2 ⟨b ⟨0, Nat.pos_of_ne_zero hn0⟩,
          List.mem_map.2 ⟨⟨0, Nat.pos_of_ne_zero hn0⟩, List.mem_finRange _, rfl⟩, hQ0 _⟩)
      rw [complexVolume_def, smul_mul_smul_comm, ← map_mul, volumeElement_eq o b hb hQb,
        prod_map_ι_sq_scalar hl, hprod]
      simp
    have hker : ∀ ν : ℂ, ν ≠ 0 →
        (Algebra.lsmul ℂ ℂ E (complexVolume Q o)).eigenspace ν = ⊥ := by
      intro ν hν
      refine (Submodule.eq_bot_iff _).2 fun ψ hψ ↦ ?_
      simp only [mem_eigenspace_iff, Algebra.lsmul_coe] at hψ
      have h0 : ν • ν • ψ = 0 := by
        calc ν • ν • ψ = ν • complexVolume Q o • ψ := by rw [hψ]
          _ = complexVolume Q o • ν • ψ := smul_comm _ _ _
          _ = complexVolume Q o • complexVolume Q o • ψ := by rw [hψ]
          _ = 0 := by rw [← mul_smul, hsq, zero_smul]
      exact (smul_eq_zero.1 ((smul_eq_zero.1 h0).resolve_left hν)).resolve_left hν
    by_cases hμ : μ = 0
    · rw [hμ, neg_zero]
    · rw [hker μ hμ, hker (-μ) (neg_ne_zero.2 hμ)]
  · obtain ⟨u, hu⟩ := not_forall.1 hQ0
    set c := ι (Q.baseChange ℂ) (1 ⊗ₜ u)
    -- The vector `u` has `c² = Q u ≠ 0`.
    have hc : c * c = algebraMap ℂ _ (Q u : ℂ) := by
      rw [ι_sq_scalar, QuadraticForm.baseChange_tmul]
      simp [Algebra.algebraMap_eq_smul_one]
    have hq : (Q u : ℂ) ≠ 0 := by exact_mod_cast hu
    have h₁ : c * ((Q u : ℂ)⁻¹ • c) = 1 := by
      rw [mul_smul_comm, hc, Algebra.algebraMap_eq_smul_one, smul_smul, inv_mul_cancel₀ hq,
        one_smul]
    have h₂ : ((Q u : ℂ)⁻¹ • c) * c = 1 := by
      rw [smul_mul_assoc, hc, Algebra.algebraMap_eq_smul_one, smul_smul, inv_mul_cancel₀ hq,
        one_smul]
    let e : E ≃ₗ[ℂ] E := .ofLinearMap (Algebra.lsmul ℂ ℂ E c)
      (Algebra.lsmul ℂ ℂ E ((Q u : ℂ)⁻¹ • c))
      (LinearMap.ext fun ψ ↦ by
        simp only [LinearMap.comp_apply, Algebra.lsmul_coe, LinearMap.id_apply]
        rw [← mul_smul, h₁, one_smul])
      (LinearMap.ext fun ψ ↦ by
        simp only [LinearMap.comp_apply, Algebra.lsmul_coe, LinearMap.id_apply]
        rw [← mul_smul, h₂, one_smul])
    refine finrank_genEigenspace_neg_of_anticommute e ?_ μ 1
    have hanti : complexVolume Q o * c + c * complexVolume Q o = 0 := by
      rw [complexVolume_mul_ι_of_even o hn, neg_add_cancel]
    ext ψ
    simp [e, ← mul_smul, ← add_smul, hanti]

/-! ### The half-spin spaces of a spinor module -/

variable {S : Type*} [AddCommGroup S] [Module ℂ S] [Module (CliffordAlgebra (Q.baseChange ℂ)) S]
  [IsScalarTower ℂ (CliffordAlgebra (Q.baseChange ℂ)) S]
  (h : Function.Bijective
    (Algebra.lsmul ℂ ℂ S : CliffordAlgebra (Q.baseChange ℂ) →ₐ[ℂ] Module.End ℂ S))

include h in
/-- **The half-spin spaces of a spinor module**: in even positive dimension, both eigenspaces of
`Γ` on a spinor module have dimension `2 ^ (n / 2 - 1)`. -/
theorem finrank_eigenspace_complexVolume_of_bijective_lsmul (hn : Even n) (hn0 : n ≠ 0) {μ : ℂ}
    (hμ : μ = 1 ∨ μ = -1) :
    finrank ℂ ((Algebra.lsmul ℂ ℂ S (complexVolume Q o)).eigenspace μ) = 2 ^ (n / 2 - 1) := by
  have hV : finrank ℂ (ℂ ⊗[ℝ] V) = n := by
    rw [Module.finrank_baseChange, Fact.out (p := finrank ℝ V = n)]
  have hS : finrank ℂ S = 2 ^ (n / 2) := by
    rw [finrank_eq_two_pow_of_bijective_lsmul _ h, hV]
  have : FiniteDimensional ℂ S := Module.finite_of_finrank_pos (by rw [hS]; positivity)
  have hsum := Submodule.finrank_add_eq_of_isCompl (isCompl_eigenspace_complexVolume (E := S) o hQ)
  rw [hS, finrank_eigenspace_complexVolume_neg o hn hn0 1] at hsum
  have hpow : 2 ^ (n / 2) = 2 * 2 ^ (n / 2 - 1) := by
    rw [← pow_succ']
    congr 1
    obtain ⟨m, rfl⟩ := hn
    omega
  have h1 : finrank ℂ ((Algebra.lsmul ℂ ℂ S (complexVolume Q o)).eigenspace 1) =
      2 ^ (n / 2 - 1) := by
    omega
  rcases hμ with rfl | rfl
  · exact h1
  · rw [finrank_eigenspace_complexVolume_neg o hn hn0 1, h1]

include h in
/-- **The half-spinors of an arbitrary module**: in even positive dimension, each eigenspace of
`Γ` on a module `E` has dimension `2 ^ (n / 2 - 1)` times the dimension of the multiplicity space
`S →ₗ[Cℓ] E` of a spinor module `S`; the underlying isomorphism `E^± ≃ S^± ⊗ Hom_Cℓ(S, E)` is
`TauCeti.eigenspaceTensorEquivOfBijective h (complexVolume Q o) (±1)`. -/
theorem finrank_eigenspace_complexVolume_eq_mul_finrank_linearMap (hn0 : n ≠ 0)
    {μ : ℂ} (hμ : μ = 1 ∨ μ = -1) :
    finrank ℂ ((Algebra.lsmul ℂ ℂ E (complexVolume Q o)).eigenspace μ) =
      2 ^ (n / 2 - 1) * finrank ℂ (S →ₗ[CliffordAlgebra (Q.baseChange ℂ)] E) := by
  have hV : finrank ℂ (ℂ ⊗[ℝ] V) = n := by
    rw [Module.finrank_baseChange, Fact.out (p := finrank ℝ V = n)]
  have hn : Even n := hV ▸ even_finrank_of_algEquiv_end _ (AlgEquiv.ofBijective _ h)
  have hS : finrank ℂ S = 2 ^ (n / 2) := by
    rw [finrank_eq_two_pow_of_bijective_lsmul _ h, hV]
  have : FiniteDimensional ℂ S := Module.finite_of_finrank_pos (by rw [hS]; positivity)
  rw [finrank_eigenspace_eq_finrank_mul_finrank_linearMap_of_bijective_lsmul h,
    finrank_eigenspace_complexVolume_of_bijective_lsmul o hQ h hn hn0 hμ]

end Form

end CliffordAlgebra
