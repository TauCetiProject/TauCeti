/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import Mathlib.Analysis.InnerProductSpace.ProdL2
public import Mathlib.LinearAlgebra.TensorProduct.Prod
public import TauCeti.LinearAlgebra.CliffordAlgebra.Even.EquivEven
public import TauCeti.LinearAlgebra.CliffordAlgebra.VolumeElement.Eigenspace
import TauCeti.LinearAlgebra.CliffordAlgebra.Functoriality

/-!
# The odd volume element under the dimension-raising equivalence

Let `V` be an oriented real inner product space of odd dimension `n = 2ℓ + 1` with a quadratic
form `Q`, and let `V ⊕ ℝ` be the `L²` product `WithLp 2 (V × ℝ)`, carrying the form
`Q₁ (m, r) = Q m - r²` of Mathlib's `CliffordAlgebra.EquivEven.Q'`. Write `e₀ = (0, 1)` for the
new unit vector. For the negative-metric convention `Q v = -‖v‖²` the form `Q₁` is again
`Q₁ x = -‖x‖²` (`CliffordAlgebra.EquivEven.Q'_ofLp_eq_neg_norm_sq`). Mathlib's
`CliffordAlgebra.toEven` identifies `Cℓ(V, Q)` with the even part of `Cℓ(V × ℝ, Q')`; over `ℂ`
it is the identification `Cℓₙ ≅ Cℓ⁰ₙ₊₁` that compares the odd Clifford modules of `V` with the
half-spin modules of `V ⊕ ℝ`.

This file complexifies that comparison and computes it on volume elements. The complexified
algebra of `Q` is `Cℓ(ℂ ⊗ V, Q_ℂ)`, and `toEven (Q.baseChange ℂ)` lands in the even part of
`Cℓ((ℂ ⊗ V) × ℂ, Q'(Q_ℂ))`. The quadratic isometry
`CliffordAlgebra.EquivEven.complexProdIsometryEquiv` between `ℂ ⊗ (V ⊕ ℝ)` with `Q₁_ℂ` and
`(ℂ ⊗ V) × ℂ` with `Q'(Q_ℂ)` (distributing the tensor product over the product) identifies the
target with the complexified Clifford algebra of `V ⊕ ℝ`. The resulting map
`ψ : Cℓ(ℂ ⊗ V, Q_ℂ) → Cℓ(ℂ ⊗ (V ⊕ ℝ), Q₁_ℂ)` sends `c(v)` to `c(e₀) c(v)`.

The main result pins the normalized volume elements of `CliffordAlgebra.complexVolume` against
each other. Let `e₁, …, eₙ` be a positively oriented orthonormal basis of `V` that is orthogonal
for `Q` (automatic when `Q v = -‖v‖²`), and orient `V ⊕ ℝ` by `(e₁, …, eₙ, e₀)`, which puts `e₀`
last as Mathlib's `Q'` does. Then

  `ψ(ω_ℂ) = -Γ_(V ⊕ ℝ)`,

where `ω_ℂ = i^(ℓ+1) c(e₁) ⋯ c(eₙ)` is the central volume element of `V` and
`Γ_(V ⊕ ℝ) = i^(ℓ+1) c(e₁) ⋯ c(eₙ) c(e₀)` the chirality element of `V ⊕ ℝ`. If instead `e₀` is
put first, the sign disappears: `ψ(ω_ℂ) = Γ_(V ⊕ ℝ)` for the orientation `(e₀, e₁, …, eₙ)`.
Moving `e₀` to the front is a cyclic permutation of the `n + 1` basis vectors, which is odd
because `n + 1` is even, so the two orientations are opposite and the two labels are exchanged.

Consequently, on any module `E` over `Cℓ(ℂ ⊗ (V ⊕ ℝ), Q₁_ℂ)`, each eigenspace `E^μ` of `Γ` is
stable under the image of `ψ`, since that image is even, and for the orientation
`(e₁, …, eₙ, e₀)` the element `ω_ℂ` acts on `E^μ` through `ψ` by `-μ`. Thus `Cℓ(ℂ ⊗ V, Q_ℂ)`
acts through `ψ` on the negative half-spinors `E⁻` with `ω_ℂ = 1`, and on the positive
half-spinors `E⁺` with `ω_ℂ = -1`.

## Main definitions

* `CliffordAlgebra.EquivEven.complexProdIsometryEquiv`: the quadratic isometry
  `ℂ ⊗ (V ⊕ ℝ) ≃ (ℂ ⊗ V) × ℂ` from `Q₁_ℂ` to `Q'(Q_ℂ)`.

## Main results

* `CliffordAlgebra.EquivEven.equivOfIsometry_toEven_ι`: `ψ(c(v)) = c(e₀) c(v)`.
* `CliffordAlgebra.EquivEven.equivOfIsometry_toEven_complexVolume`: `ψ(ω_ℂ) = -Γ_(V ⊕ ℝ)` for the
  orientation `(e₁, …, eₙ, e₀)`.
* `CliffordAlgebra.EquivEven.equivOfIsometry_toEven_complexVolume_of_cons`: `ψ(ω_ℂ) = Γ_(V ⊕ ℝ)`
  for the orientation `(e₀, e₁, …, eₙ)`.
* `CliffordAlgebra.EquivEven.equivOfIsometry_toEven_smul_mem_eigenspace_complexVolume`: the image
  of `ψ` preserves each eigenspace `E^μ` of `Γ_(V ⊕ ℝ)`.
* `CliffordAlgebra.EquivEven.equivOfIsometry_toEven_complexVolume_smul`: `ω_ℂ` acts on `E^μ`
  through `ψ` by `-μ`.

## References

* H. B. Lawson and M.-L. Michelsohn, *Spin Geometry* (1989), Chapter I, §3 and §5.
-/

public section

noncomputable section

open Module
open scoped TensorProduct

namespace CliffordAlgebra

namespace EquivEven

variable {V : Type*} [NormedAddCommGroup V] [InnerProductSpace ℝ V]
  {Q : QuadraticForm ℝ V} {Q₁ : QuadraticForm ℝ (WithLp 2 (V × ℝ))}

/-- For the negative-metric convention `Q v = -‖v‖²`, the form `Q' Q` on the `L²` product
`V ⊕ ℝ` is again `x ↦ -‖x‖²`, so `Q₁ x = -‖x‖²` satisfies the hypothesis
`Q₁ x = Q' Q (WithLp.ofLp x)` of the results below. -/
theorem Q'_ofLp_eq_neg_norm_sq (hQ : ∀ v, Q v = -‖v‖ ^ 2) (x : WithLp 2 (V × ℝ)) :
    Q' Q (WithLp.ofLp x) = -‖x‖ ^ 2 := by
  simp only [Q'_apply, hQ, WithLp.prod_norm_sq_eq_of_L2, WithLp.ofLp_fst, WithLp.ofLp_snd,
    Real.norm_eq_abs, sq_abs]
  ring

/-! ### Complexifying `V ⊕ ℝ` -/

/-- The linear equivalence `ℂ ⊗ (V ⊕ ℝ) ≃ (ℂ ⊗ V) × ℂ`, `z ⊗ (m, r) ↦ (z ⊗ m, r z)`. -/
private def complexProdEquiv : ℂ ⊗[ℝ] WithLp 2 (V × ℝ) ≃ₗ[ℂ] (ℂ ⊗[ℝ] V) × ℂ :=
  (WithLp.linearEquiv 2 ℝ (V × ℝ)).baseChange ℝ ℂ _ _ ≪≫ₗ
    TensorProduct.prodRight ℝ ℂ ℂ V ℝ ≪≫ₗ
    (LinearEquiv.refl ℂ _).prodCongr (TensorProduct.AlgebraTensorModule.rid ℝ ℂ ℂ)

private theorem complexProdEquiv_tmul (z : ℂ) (x : WithLp 2 (V × ℝ)) :
    complexProdEquiv (z ⊗ₜ x) = (z ⊗ₜ (WithLp.ofLp x).1, (WithLp.ofLp x).2 • z) := by
  simp [complexProdEquiv]

variable (hQ₁ : ∀ x, Q₁ x = Q' Q (WithLp.ofLp x))
include hQ₁

/-- **The complexification of `V ⊕ ℝ`**: when `Q₁` is the form `Q₁ (m, r) = Q m - r²` on the
`L²` product `V ⊕ ℝ`, the map `z ⊗ (m, r) ↦ (z ⊗ m, r z)` is a quadratic isometry from
`ℂ ⊗ (V ⊕ ℝ)` with `Q₁_ℂ` onto `(ℂ ⊗ V) × ℂ` with `Q'(Q_ℂ)`, the form Mathlib's
`CliffordAlgebra.toEven` uses for `Q_ℂ`. -/
def complexProdIsometryEquiv : (Q₁.baseChange ℂ).IsometryEquiv (Q' (Q.baseChange ℂ)) where
  toLinearEquiv := complexProdEquiv
  map_app' := by
    have h : (Q' (Q.baseChange ℂ)).comp complexProdEquiv.toLinearMap = Q₁.baseChange ℂ := by
      ext x
      simp [complexProdEquiv_tmul, hQ₁, Algebra.smul_def]
    exact fun x ↦ congr($h x)

@[simp]
theorem complexProdIsometryEquiv_tmul (z : ℂ) (x : WithLp 2 (V × ℝ)) :
    complexProdIsometryEquiv hQ₁ (z ⊗ₜ x) = (z ⊗ₜ (WithLp.ofLp x).1, (WithLp.ofLp x).2 • z) :=
  complexProdEquiv_tmul z x

/-- The Clifford algebra equivalence induced by `complexProdIsometryEquiv` sends `v(z ⊗ m)`, the
generator of `(z ⊗ m, 0)`, to the generator of `z ⊗ (m, 0)`. This is not a `simp` lemma, because
`simp` rewrites `equivOfIsometry e x` to `map e.toIsometry x` by `equivOfIsometry_apply`. -/
theorem equivOfIsometry_v (z : ℂ) (m : V) :
    equivOfIsometry (complexProdIsometryEquiv hQ₁).symm (v (Q.baseChange ℂ) (z ⊗ₜ m)) =
      ι (Q₁.baseChange ℂ) (z ⊗ₜ WithLp.toLp 2 (m, 0)) := by
  rw [v, LinearMap.comp_apply, LinearMap.inl_apply, equivOfIsometry_apply, map_apply_ι]
  exact congrArg _ ((QuadraticMap.IsometryEquiv.symm_apply_eq _).2 (by simp))

/-- The Clifford algebra equivalence induced by `complexProdIsometryEquiv` sends `e₀`, the
generator of `(0, 1)`, to the generator of `1 ⊗ (0, 1)`. Like
`CliffordAlgebra.EquivEven.equivOfIsometry_v`, this is not a `simp` lemma. -/
theorem equivOfIsometry_e0 :
    equivOfIsometry (complexProdIsometryEquiv hQ₁).symm (e0 (Q.baseChange ℂ)) =
      ι (Q₁.baseChange ℂ) (1 ⊗ₜ WithLp.toLp 2 (0, 1)) := by
  rw [e0, equivOfIsometry_apply, map_apply_ι]
  exact congrArg _ ((QuadraticMap.IsometryEquiv.symm_apply_eq _).2 (by simp))

/-- **The complexified dimension-raising map on generators**: `ψ(c(z ⊗ m)) = c(e₀) c(z ⊗ m)`,
where `e₀ = 1 ⊗ (0, 1)` and `m` is included in `V ⊕ ℝ` as `(m, 0)`. -/
theorem equivOfIsometry_toEven_ι (z : ℂ) (m : V) :
    equivOfIsometry (complexProdIsometryEquiv hQ₁).symm
        (toEven (Q.baseChange ℂ) (ι (Q.baseChange ℂ) (z ⊗ₜ m))) =
      ι (Q₁.baseChange ℂ) (1 ⊗ₜ WithLp.toLp 2 (0, 1)) *
        ι (Q₁.baseChange ℂ) (z ⊗ₜ WithLp.toLp 2 (m, 0)) := by
  rw [toEven_ι, map_mul, equivOfIsometry_e0, equivOfIsometry_v]

/-! ### The volume elements -/

/-- The polar form of `Q₁ (m, r) = Q m - r²` is `((m, r), (m', r')) ↦ B_Q(m, m') - r r'`. -/
private theorem associated_apply_eq (x y : WithLp 2 (V × ℝ)) :
    QuadraticMap.associated Q₁ x y =
      QuadraticMap.associated Q (WithLp.ofLp x).1 (WithLp.ofLp y).1 -
        (WithLp.ofLp x).2 * (WithLp.ofLp y).2 := by
  rw [show Q₁ = (Q' Q).comp (WithLp.linearEquiv 2 ℝ (V × ℝ)).toLinearMap from
    QuadraticMap.ext hQ₁, QuadraticMap.associated_comp, QuadraticMap.associated_prod]
  simp [sub_eq_add_neg]

/-- Appending `e₀` to a `Q`-orthogonal basis of `V` gives a `Q₁`-orthogonal basis of `V ⊕ ℝ`. -/
private theorem isOrthoᵢ_associated_prod {ι : Type*} [Fintype ι] (b : OrthonormalBasis ι ℝ V)
    (hQb : (QuadraticMap.associated Q).IsOrthoᵢ b.toBasis) {κ : Type*} [Fintype κ]
    (e : ι ⊕ Fin 1 ≃ κ) :
    (QuadraticMap.associated Q₁).IsOrthoᵢ
      ((b.prod (OrthonormalBasis.singleton (Fin 1) ℝ)).reindex e).toBasis := by
  rw [LinearMap.isOrthoᵢ_def] at hQb ⊢
  intro i j hij
  have hij' : e.symm i ≠ e.symm j := e.symm.injective.ne hij
  simp only [OrthonormalBasis.coe_toBasis, OrthonormalBasis.reindex_apply,
    associated_apply_eq hQ₁]
  generalize e.symm i = p, e.symm j = q at hij'
  rcases p with p | p <;> rcases q with q | q
  · simpa using hQb p q (Sum.inl.inj_iff.not.1 hij')
  · simp
  · simp
  · exact absurd (congrArg Sum.inr (Subsingleton.elim p q)) hij'

/-- The complexified dimension-raising map on an ordered product of an odd number of real
vectors: `ψ(c(m₁) ⋯ c(mₙ)) = c(e₀) c(m₁) ⋯ c(mₙ)`. -/
private theorem equivOfIsometry_toEven_prod {l : List V} (hl : Odd l.length) :
    equivOfIsometry (complexProdIsometryEquiv hQ₁).symm
        (toEven (Q.baseChange ℂ) ((l.map fun m ↦ ι (Q.baseChange ℂ) (1 ⊗ₜ m)).prod)) =
      ι (Q₁.baseChange ℂ) (1 ⊗ₜ WithLp.toLp 2 (0, 1)) *
        (l.map fun m ↦ ι (Q₁.baseChange ℂ) (1 ⊗ₜ WithLp.toLp 2 (m, 0))).prod := by
  have h := coe_toEven_of_mem_odd (prod_map_ι_mem_evenOdd_one_of_odd_length
    (Q := Q.baseChange ℂ) (l := l.map ((1 : ℂ) ⊗ₜ ·)) (by simpa using hl))
  rw [map_inl_prod_map_ι] at h
  simp only [List.map_map, Function.comp_def] at h
  rw [h, map_mul, equivOfIsometry_e0, map_list_prod, List.map_map]
  simp only [Function.comp_def, equivOfIsometry_v]

/-- The same product with `c(e₀)` moved to the end: `ψ(c(m₁) ⋯ c(mₙ)) = -c(m₁) ⋯ c(mₙ) c(e₀)`
for `n` odd. -/
private theorem equivOfIsometry_toEven_prod_eq_neg_mul {l : List V} (hl : Odd l.length) :
    equivOfIsometry (complexProdIsometryEquiv hQ₁).symm
        (toEven (Q.baseChange ℂ) ((l.map fun m ↦ ι (Q.baseChange ℂ) (1 ⊗ₜ m)).prod)) =
      -((l.map fun m ↦ ι (Q₁.baseChange ℂ) (1 ⊗ₜ WithLp.toLp 2 (m, 0))).prod *
        ι (Q₁.baseChange ℂ) (1 ⊗ₜ WithLp.toLp 2 (0, 1))) := by
  have h := coe_toEven_prod_map_ι_of_odd_length (Q := Q.baseChange ℂ)
    (l := l.map ((1 : ℂ) ⊗ₜ ·)) (by simpa using hl)
  simp only [List.map_map, Function.comp_def] at h
  rw [h, map_neg, map_mul, equivOfIsometry_e0, map_list_prod, List.map_map]
  simp only [Function.comp_def, equivOfIsometry_v]

variable [FiniteDimensional ℝ V] {n : ℕ} [Fact (finrank ℝ V = n)]
  [Fact (finrank ℝ (WithLp 2 (V × ℝ)) = n + 1)]
  (o : Orientation ℝ V (Fin n)) (o' : Orientation ℝ (WithLp 2 (V × ℝ)) (Fin (n + 1)))

/-- **The odd volume element is minus the chirality element of `V ⊕ ℝ`**: for `n` odd, a
positively oriented orthonormal basis `e₁, …, eₙ` of `V` orthogonal for `Q`, and `V ⊕ ℝ` oriented
by `(e₁, …, eₙ, e₀)`, the complexified dimension-raising map `ψ` sends the normalized volume
element `ω_ℂ` of `V` to minus the normalized volume element `Γ` of `V ⊕ ℝ`. -/
theorem equivOfIsometry_toEven_complexVolume (hn : Odd n) (b : OrthonormalBasis (Fin n) ℝ V)
    (hb : b.toBasis.orientation = o) (hQb : (QuadraticMap.associated Q).IsOrthoᵢ b.toBasis)
    (ho' : ((b.prod (OrthonormalBasis.singleton (Fin 1) ℝ)).reindex
      finSumFinEquiv).toBasis.orientation = o') :
    equivOfIsometry (complexProdIsometryEquiv hQ₁).symm
        (toEven (Q.baseChange ℂ) (complexVolume Q o)) = -complexVolume Q₁ o' := by
  have hexp : (n + 1 + 1) / 2 = (n + 1) / 2 := by obtain ⟨k, rfl⟩ := hn; omega
  rw [complexVolume_eq o b hb hQb, complexVolume_eq o' _ ho' (isOrthoᵢ_associated_prod hQ₁ b hQb _),
    hexp, map_smul, Subalgebra.coe_smul, map_smul,
    equivOfIsometry_toEven_prod_eq_neg_mul hQ₁ (by simpa using hn), List.finRange_succ_last]
  simp [Function.comp_def, smul_neg, finSumFinEquiv_symm_apply_castSucc]

/-- **Putting `e₀` first removes the sign**: for `n` odd, a positively oriented orthonormal basis
`e₁, …, eₙ` of `V` orthogonal for `Q`, and `V ⊕ ℝ` oriented by `(e₀, e₁, …, eₙ)`, the
complexified dimension-raising map `ψ` sends the normalized volume element `ω_ℂ` of `V` to the
normalized volume element `Γ` of `V ⊕ ℝ`. Since `n` is odd, this orientation is opposite to the
one of `CliffordAlgebra.EquivEven.equivOfIsometry_toEven_complexVolume`. -/
theorem equivOfIsometry_toEven_complexVolume_of_cons (hn : Odd n)
    (b : OrthonormalBasis (Fin n) ℝ V) (hb : b.toBasis.orientation = o)
    (hQb : (QuadraticMap.associated Q).IsOrthoᵢ b.toBasis)
    (ho' : ((b.prod (OrthonormalBasis.singleton (Fin 1) ℝ)).reindex
      (((Equiv.sumComm _ _).trans finSumFinEquiv).trans
        (finCongr (add_comm 1 n)))).toBasis.orientation = o') :
    equivOfIsometry (complexProdIsometryEquiv hQ₁).symm
        (toEven (Q.baseChange ℂ) (complexVolume Q o)) = complexVolume Q₁ o' := by
  set e : Fin n ⊕ Fin 1 ≃ Fin (n + 1) :=
    ((Equiv.sumComm _ _).trans finSumFinEquiv).trans (finCongr (add_comm 1 n))
  have he0 : e.symm 0 = Sum.inr 0 := (Equiv.symm_apply_eq _).2 (Fin.ext (by simp [e]))
  have hes (i : Fin n) : e.symm i.succ = Sum.inl i :=
    (Equiv.symm_apply_eq _).2 (Fin.ext (by simp [e]))
  have hexp : (n + 1 + 1) / 2 = (n + 1) / 2 := by obtain ⟨k, rfl⟩ := hn; omega
  rw [complexVolume_eq o b hb hQb, complexVolume_eq o' _ ho' (isOrthoᵢ_associated_prod hQ₁ b hQb _),
    hexp, map_smul, Subalgebra.coe_smul, map_smul,
    equivOfIsometry_toEven_prod hQ₁ (by simpa using hn), List.finRange_succ]
  simp [Function.comp_def, he0, hes]

/-! ### Restricting modules along the dimension-raising map -/

variable {E : Type*} [AddCommGroup E] [Module ℂ E] [Module (CliffordAlgebra (Q₁.baseChange ℂ)) E]
  [IsScalarTower ℂ (CliffordAlgebra (Q₁.baseChange ℂ)) E]

omit [Fact (finrank ℝ V = n)] in
/-- **The image of `ψ` preserves the half-spinors of `V ⊕ ℝ`**: every element `ψ(x)` of the
image of the complexified dimension-raising map is even, so it maps each eigenspace of the
normalized volume element `Γ` of `V ⊕ ℝ` on a module `E` to itself, for either orientation. -/
theorem equivOfIsometry_toEven_smul_mem_eigenspace_complexVolume
    (x : CliffordAlgebra (Q.baseChange ℂ)) {μ : ℂ} {ψ : E}
    (hψ : ψ ∈ (Algebra.lsmul ℂ ℂ E (complexVolume Q₁ o')).eigenspace μ) :
    equivOfIsometry (complexProdIsometryEquiv hQ₁).symm (toEven (Q.baseChange ℂ) x) • ψ ∈
      (Algebra.lsmul ℂ ℂ E (complexVolume Q₁ o')).eigenspace μ := by
  refine smul_mem_eigenspace_complexVolume_of_mem_even o' ?_ hψ
  rw [← even_toSubmodule, Subalgebra.mem_toSubmodule, equivOfIsometry_apply]
  exact map_mem_even _ (toEven (Q.baseChange ℂ) x).2

/-- **The label of the restricted half-spinors**: for `n` odd and `V ⊕ ℝ` oriented by
`(e₁, …, eₙ, e₀)`, the volume element `ω_ℂ` of `V` acts through `ψ` by `-μ` on the
`μ`-eigenspace of the chirality element `Γ` of `V ⊕ ℝ` in any module `E`. Together with
`CliffordAlgebra.EquivEven.equivOfIsometry_toEven_smul_mem_eigenspace_complexVolume`, this says
that `Cℓ(ℂ ⊗ V, Q_ℂ)` acts through `ψ` on the negative half-spinors with `ω_ℂ = 1`, and on the
positive half-spinors with `ω_ℂ = -1`. -/
theorem equivOfIsometry_toEven_complexVolume_smul (hn : Odd n)
    (b : OrthonormalBasis (Fin n) ℝ V) (hb : b.toBasis.orientation = o)
    (hQb : (QuadraticMap.associated Q).IsOrthoᵢ b.toBasis)
    (ho' : ((b.prod (OrthonormalBasis.singleton (Fin 1) ℝ)).reindex
      finSumFinEquiv).toBasis.orientation = o')
    {μ : ℂ} {ψ : E} (hψ : ψ ∈ (Algebra.lsmul ℂ ℂ E (complexVolume Q₁ o')).eigenspace μ) :
    equivOfIsometry (complexProdIsometryEquiv hQ₁).symm
        (toEven (Q.baseChange ℂ) (complexVolume Q o)) • ψ = -μ • ψ := by
  simp only [Module.End.mem_eigenspace_iff, Algebra.lsmul_coe] at hψ
  rw [equivOfIsometry_toEven_complexVolume hQ₁ o o' hn b hb hQb ho', neg_smul, hψ, neg_smul]

end EquivEven

end CliffordAlgebra
