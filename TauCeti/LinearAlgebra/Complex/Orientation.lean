/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import Mathlib.LinearAlgebra.Complex.Orientation
public import Mathlib.RingTheory.AlgebraTower
public import TauCeti.LinearAlgebra.Complex.Determinant
public import TauCeti.LinearAlgebra.Complex.Finrank
public import TauCeti.LinearAlgebra.Complex.Module
public import TauCeti.LinearAlgebra.Orientation.Prod

/-!
# The canonical real orientation of a complex vector space

A complex basis `b` of a complex vector space `E` determines the real basis
`(b₀, I • b₀, b₁, I • b₁, …)` of `E` (`Module.Basis.complexToReal`). The real change-of-basis
determinant between two such real bases is the squared modulus of the complex one
(`Module.Basis.det_complexToReal`), so it is positive and all complex bases induce the same real
orientation. A finite-dimensional complex vector space therefore carries a canonical real
orientation `TauCeti.complexOrientation E`, which involves no choice of basis. Complex-linear
equivalences transport it, so complex-linear automorphisms preserve it. On `ℂ` itself it is
Mathlib's standard orientation `Complex.orientation`.

The canonical orientation of a product `E × F` is the ordered product `Orientation.prod` of the
canonical orientations of the factors, the first factor's directions before the second's: the
real basis underlying the complex product basis `(b, c)` is the real basis of `b` followed by that
of `c`. Exchanging two factors of real dimensions `m` and `n` multiplies a product orientation by
`(-1) ^ (m * n)`; for complex factors both real dimensions are even, so the exchange carries the
product of the canonical orientations of `E` and `F` to that of `F` and `E`.

This is the linear model for the canonical orientation of a complex manifold, whose chart
transitions have complex-linear derivatives.

A conjugate-linear equivalence `f`, by contrast, reverses the canonical orientation once per
complex dimension: it carries the real basis `(b₀, I • b₀, b₁, I • b₁, …)` to
`(f b₀, -(I • f b₀), f b₁, -(I • f b₁), …)`, whose orientation is `(-1) ^ n` times the canonical
one, `n` being the complex dimension. Equivalently the real determinant of a conjugate-linear
automorphism has the sign `(-1) ^ n`. This is the complex factor of the determinant-line sign of
charge conjugation in Seiberg–Witten theory: the antilinear intertwiner `ψ ↦ j ψ` between the
Dirac operators of a `Spinᶜ` structure and of its conjugate maps the complex kernel and cokernel
conjugate-linearly, so it changes their canonical orientations by `(-1) ^ (dim ker)` and
`(-1) ^ (dim coker)`, together `(-1) ^ ind_ℂ D`.

The real module structure of `E` is an ambient one compatible with the complex structure
(`IsScalarTower ℝ ℂ E`), as for a complex normed space or a real space with a complex structure.

## Main definitions

* `Module.Basis.complexToReal`: the real basis `(b i, I • b i)` underlying a complex basis `b`.
* `TauCeti.complexOrientation`: the canonical real orientation of a complex vector space, indexed
  by `Fin (2 * finrank ℂ E)`.

## Main results

* `Module.Basis.det_complexToReal`: the real determinant between the real bases underlying two
  complex bases is the squared modulus of their complex determinant.
* `Module.Basis.orientation_complexToReal_eq`: all complex bases give the same real orientation.
* `Module.Basis.complexOrientation_eq`: every complex basis computes the canonical orientation.
* `LinearEquiv.map_complexOrientation`: complex-linear equivalences transport canonical
  orientations.
* `TauCeti.reindex_complexOrientation_complex`: on `ℂ`, the canonical orientation is
  `Complex.orientation`.
* `TauCeti.prod_complexOrientation`: the product of the canonical orientations of `E` and `F` is
  the canonical orientation of `E × F`.
* `TauCeti.map_prodComm_prod_complexOrientation`: exchanging the factors carries the product of
  canonical orientations of `E` and `F` to that of `F` and `E`, with sign `1`.
* `LinearEquiv.map_toRealLinearEquiv_complexOrientation`: a conjugate-linear equivalence multiplies
  canonical orientations by `(-1) ^ n`, `n` the complex dimension.
* `LinearEquiv.neg_one_pow_mul_det_toRealLinearEquiv_pos`: the real determinant of a
  conjugate-linear automorphism has the sign `(-1) ^ n`.

## References

* R. Bott and L. W. Tu, *Differential Forms in Algebraic Topology*, §1.
* C. H. Taubes, *The Seiberg–Witten and Gromov invariants*, Math. Res. Lett. 2 (1995), 221–238,
  for the comparison of the invariants of a `Spinᶜ` structure and of its conjugate.
* D. Huybrechts, *Complex Geometry: An Introduction*, §1.2.
-/

public section

open Module

namespace Module.Basis

variable {ι ι' E F : Type*}
  [AddCommGroup E] [Module ℂ E] [Module ℝ E] [IsScalarTower ℝ ℂ E]
  [AddCommGroup F] [Module ℂ F] [Module ℝ F] [IsScalarTower ℝ ℂ F]

/-- The real basis underlying a complex basis `b`: its vectors are `b i` at index `(i, 0)` and
`I • b i` at index `(i, 1)`. -/
noncomputable def complexToReal (b : Basis ι ℂ E) : Basis (ι × Fin 2) ℝ E :=
  Complex.basisOneI.smulTower' b

/-- The vectors of the real basis `b.complexToReal` are `Complex.basisOneI k • b i`, that is,
`b i` and `I • b i`. -/
@[simp]
theorem complexToReal_apply (b : Basis ι ℂ E) (i : ι) (k : Fin 2) :
    b.complexToReal (i, k) = Complex.basisOneI k • b i :=
  smulTower'_apply _ _ _

/-- The real coordinates of a vector in the basis `b.complexToReal` are the real and imaginary
parts of its complex coordinates in `b`. -/
@[simp]
theorem complexToReal_repr_apply (b : Basis ι ℂ E) (x : E) (i : ι) (k : Fin 2) :
    b.complexToReal.repr x (i, k) = Complex.basisOneI.repr (b.repr x i) k :=
  smulTower'_repr _ _ _ _

/-- The real basis underlying a complex basis is natural in complex-linear equivalences. -/
theorem complexToReal_map (b : Basis ι ℂ E) (f : E ≃ₗ[ℂ] F) :
    (b.map f).complexToReal = b.complexToReal.map (f.restrictScalars ℝ) :=
  eq_of_apply_eq fun ⟨i, k⟩ ↦ by simp

/-- Reindexing a complex basis reindexes its underlying real basis. -/
theorem complexToReal_reindex (b : Basis ι ℂ E) (e : ι ≃ ι') :
    (b.reindex e).complexToReal = b.complexToReal.reindex (e.prodCongr (Equiv.refl _)) :=
  eq_of_apply_eq fun ⟨i, k⟩ ↦ by simp

variable [Fintype ι] [DecidableEq ι]

/-- The real determinant between the real bases underlying two complex bases is the squared
modulus of their complex determinant. -/
theorem det_complexToReal (b c : Basis ι ℂ E) :
    b.complexToReal.det c.complexToReal = Complex.normSq (b.det c) := by
  -- `c` is the image of `b` under the complex-linear automorphism `f` with `f (b i) = c i`.
  set f : E ≃ₗ[ℂ] E := b.equiv c (Equiv.refl ι)
  have hc : c = b.map f := by simp [f, map_equiv]
  have hcR : ⇑c.complexToReal = (f.restrictScalars ℝ : E →ₗ[ℝ] E) ∘ b.complexToReal := by
    rw [hc, complexToReal_map, coe_map, LinearEquiv.coe_coe]
  have hcC : ⇑c = (f : E →ₗ[ℂ] E) ∘ b := by
    rw [hc, coe_map, LinearEquiv.coe_coe]
  rw [hcR, hcC]
  simp only [det_comp, det_self, mul_one]
  exact LinearMap.det_restrictScalars_eq_normSq _

/-- Any two complex bases induce the same real orientation. -/
theorem orientation_complexToReal_eq (b c : Basis ι ℂ E) :
    b.complexToReal.orientation = c.complexToReal.orientation := by
  rw [orientation_eq_iff_det_pos, det_complexToReal]
  exact Complex.normSq_pos.mpr (b.isUnit_det c).ne_zero

end Module.Basis

namespace TauCeti

variable (E : Type*) [AddCommGroup E] [Module ℂ E] [Module ℝ E] [IsScalarTower ℝ ℂ E]
  [FiniteDimensional ℂ E]

/-- The index equivalence `Fin n × Fin 2 ≃ Fin (2 * n)` sending `(i, k)` to `2 * i + k`. It orders
the real basis `b.complexToReal` as `(b₀, I • b₀, b₁, I • b₁, …)`. -/
def complexRealIndexEquiv (n : ℕ) : Fin n × Fin 2 ≃ Fin (2 * n) :=
  finProdFinEquiv.trans (finCongr (Nat.mul_comm n 2))

/-- The position of `(i, k)` under `complexRealIndexEquiv` is `2 * i + k`. -/
@[simp]
theorem complexRealIndexEquiv_apply_val (n : ℕ) (i : Fin n) (k : Fin 2) :
    (complexRealIndexEquiv n (i, k) : ℕ) = 2 * i + k := by
  simp [complexRealIndexEquiv, Nat.add_comm]

/-- Casting along an equality of real dimensions commutes with `complexRealIndexEquiv`. -/
@[simp]
theorem cast_complexRealIndexEquiv {m n : ℕ} (h : 2 * m = 2 * n) (i : Fin m) (k : Fin 2) :
    Fin.cast h (complexRealIndexEquiv m (i, k)) =
      complexRealIndexEquiv n (Fin.cast (by omega) i, k) :=
  Fin.ext (by simp)

/-- The canonical real orientation of a finite-dimensional complex vector space `E`: the
orientation of the real basis `(b₀, I • b₀, b₁, I • b₁, …)` for any complex basis `b` of `E`
(`Module.Basis.complexOrientation_eq`). -/
noncomputable def complexOrientation : Orientation ℝ E (Fin (2 * finrank ℂ E)) :=
  Orientation.reindex ℝ E (complexRealIndexEquiv _) (finBasis ℂ E).complexToReal.orientation

end TauCeti

namespace Module.Basis

variable {E : Type*} [AddCommGroup E] [Module ℂ E] [Module ℝ E] [IsScalarTower ℝ ℂ E]
  [FiniteDimensional ℂ E]

/-- The canonical real orientation is the orientation of the real basis
`(b₀, I • b₀, b₁, I • b₁, …)` underlying any complex basis `b`. -/
theorem complexOrientation_eq (b : Basis (Fin (finrank ℂ E)) ℂ E) :
    TauCeti.complexOrientation E =
      Orientation.reindex ℝ E (TauCeti.complexRealIndexEquiv _) b.complexToReal.orientation := by
  rw [TauCeti.complexOrientation, orientation_complexToReal_eq (finBasis ℂ E) b]

end Module.Basis

namespace LinearEquiv

open TauCeti

variable {E F : Type*} [AddCommGroup E] [Module ℂ E] [Module ℝ E] [IsScalarTower ℝ ℂ E]
  [FiniteDimensional ℂ E] [AddCommGroup F] [Module ℂ F] [Module ℝ F] [IsScalarTower ℝ ℂ F]
  [FiniteDimensional ℂ F]

/-- A complex-linear equivalence transports the canonical real orientation of its source to that
of its target, after identifying the index types through the equality of complex dimensions. -/
theorem map_complexOrientation (f : E ≃ₗ[ℂ] F) :
    Orientation.map _ (f.restrictScalars ℝ) (complexOrientation E) =
      Orientation.reindex ℝ F (finCongr (by rw [f.finrank_eq])) (complexOrientation F) := by
  set b := finBasis ℂ E
  rw [b.complexOrientation_eq, ((b.map f).reindex (finCongr f.finrank_eq)).complexOrientation_eq]
  simp only [← Basis.orientation_reindex, ← Basis.orientation_map, Basis.complexToReal_reindex,
    Basis.complexToReal_map]
  congr 1
  refine Basis.eq_of_apply_eq fun j ↦ ?_
  obtain ⟨⟨i, k⟩, rfl⟩ := (complexRealIndexEquiv _).surjective j
  simp

/-- Complex-linear automorphisms preserve the canonical real orientation. -/
@[simp]
theorem map_complexOrientation_self (f : E ≃ₗ[ℂ] E) :
    Orientation.map _ (f.restrictScalars ℝ) (complexOrientation E) = complexOrientation E := by
  simpa using f.map_complexOrientation

end LinearEquiv

/-! ### Conjugate-linear equivalences -/

namespace Module.Basis

variable {ι E F : Type*} [AddCommGroup E] [Module ℂ E] [Module ℝ E] [IsScalarTower ℝ ℂ E]
  [AddCommGroup F] [Module ℂ F] [Module ℝ F] [IsScalarTower ℝ ℂ F]

/-- A conjugate-linear equivalence `f` carries the real basis `(bᵢ, I • bᵢ)` underlying a complex
basis `b` to `(cᵢ, -(I • cᵢ))`, where `cᵢ = f bᵢ`: since `f (I • bᵢ) = -(I • f bᵢ)`, every second
vector changes sign. -/
theorem complexToReal_map_toRealLinearEquiv (b : Basis ι ℂ E) (c : Basis ι ℂ F) (f : E ≃ₗ⋆[ℂ] F)
    (hc : ∀ i, c i = f (b i)) :
    b.complexToReal.map f.toRealLinearEquiv =
      c.complexToReal.unitsSMul fun k ↦ (-1 : ℝˣ) ^ (k.2 : ℕ) := by
  refine Basis.eq_of_apply_eq fun ⟨i, k⟩ ↦ ?_
  fin_cases k <;> simp [hc, Basis.unitsSMul_apply, Complex.basisOneI, map_smulₛₗ]

end Module.Basis

namespace LinearEquiv

open TauCeti

variable {E F : Type*} [AddCommGroup E] [Module ℂ E] [Module ℝ E] [IsScalarTower ℝ ℂ E]
  [AddCommGroup F] [Module ℂ F] [Module ℝ F] [IsScalarTower ℝ ℂ F]

/-- A conjugate-linear equivalence preserves the complex dimension. -/
theorem finrank_eq_of_conj (f : E ≃ₗ⋆[ℂ] F) : finrank ℂ E = finrank ℂ F := by
  have := f.toRealLinearEquiv.finrank_eq
  rw [finrank_real_eq_two_mul_finrank_complex, finrank_real_eq_two_mul_finrank_complex] at this
  omega

variable [FiniteDimensional ℂ E] [FiniteDimensional ℂ F]

/-- A conjugate-linear equivalence carries the canonical real orientation of its source to
`(-1) ^ n` times that of its target, where `n` is the complex dimension, after identifying the
index types through the equality of complex dimensions. -/
theorem map_toRealLinearEquiv_complexOrientation (f : E ≃ₗ⋆[ℂ] F) :
    Orientation.map _ f.toRealLinearEquiv (complexOrientation E) =
      (-1 : ℝˣ) ^ finrank ℂ E •
        Orientation.reindex ℝ F (finCongr (by rw [finrank_eq_of_conj f]))
          (complexOrientation F) := by
  set b := finBasis ℂ E
  -- The images `f bᵢ` form a complex basis `c` of `F`, since `f` is conjugate-linear.
  have hli : LinearIndependent ℂ (f.toAddMonoidHom ∘ b) :=
    b.linearIndependent.map_of_surjective_injectiveₛ (starRingEnd ℂ) f.toAddMonoidHom
      (starRingEnd ℂ).surjective f.injective fun r m ↦ map_smulₛₗ f r m
  set c : Basis (Fin (finrank ℂ E)) ℂ F := basisOfLinearIndependentOfCardEqFinrank' _ hli
    (by rw [Fintype.card_fin]; exact finrank_eq_of_conj f)
  have hc : ∀ i, c i = f (b i) := fun i ↦ by simp [c]
  -- The `n` sign changes of `b.complexToReal_map_toRealLinearEquiv` multiply to `(-1) ^ n`.
  have hw : (∏ k : Fin (finrank ℂ E) × Fin 2, (-1 : ℝˣ) ^ (k.2 : ℕ)) = (-1) ^ finrank ℂ E := by
    rw [Fintype.prod_prod_type]
    simp [Fin.prod_univ_two]
  have hbasis : c.complexToReal.reindex (complexRealIndexEquiv (finrank ℂ E)) =
      ((c.complexToReal.reindex
        ((finCongr (finrank_eq_of_conj f)).prodCongr (Equiv.refl _))).reindex
          (complexRealIndexEquiv _)).reindex (finCongr (by rw [finrank_eq_of_conj f])) := by
    refine Basis.eq_of_apply_eq fun j ↦ ?_
    obtain ⟨⟨i, k⟩, rfl⟩ := (complexRealIndexEquiv (finrank ℂ E)).surjective j
    simp
  rw [b.complexOrientation_eq, (c.reindex (finCongr (finrank_eq_of_conj f))).complexOrientation_eq,
    Orientation.map_reindex, ← Basis.orientation_map, b.complexToReal_map_toRealLinearEquiv c f hc,
    Basis.orientation_unitsSMul, hw, Basis.complexToReal_reindex, ← Basis.orientation_reindex,
    ← Basis.orientation_reindex, ← hbasis, Basis.orientation_reindex]
  rcases Nat.even_or_odd (finrank ℂ E) with h | h <;>
    simp [h.neg_one_pow, Module.Ray.neg_units_smul, Orientation.reindex_neg]

/-- A conjugate-linear automorphism multiplies the canonical real orientation by `(-1) ^ n`, where
`n` is the complex dimension. -/
@[simp]
theorem map_toRealLinearEquiv_complexOrientation_self (f : E ≃ₗ⋆[ℂ] E) :
    Orientation.map _ f.toRealLinearEquiv (complexOrientation E) =
      (-1 : ℝˣ) ^ finrank ℂ E • complexOrientation E := by
  simpa using f.map_toRealLinearEquiv_complexOrientation

/-- The real determinant of a conjugate-linear automorphism has the sign `(-1) ^ n`, where `n` is
the complex dimension. For complex conjugation on `ℂ` this is `Complex.det_conjAe`. -/
theorem neg_one_pow_mul_det_toRealLinearEquiv_pos (f : E ≃ₗ⋆[ℂ] E) :
    0 < (-1) ^ finrank ℂ E * LinearMap.det (f.toRealLinearEquiv : E →ₗ[ℝ] E) := by
  have : FiniteDimensional ℝ E := Module.Finite.trans ℂ E
  have hcard : Fintype.card (Fin (2 * finrank ℂ E)) = finrank ℝ E := by
    simp [finrank_real_eq_two_mul_finrank_complex]
  have h := f.map_toRealLinearEquiv_complexOrientation_self
  rcases Nat.even_or_odd (finrank ℂ E) with he | ho
  · rw [he.neg_one_pow, one_smul, Orientation.map_eq_iff_det_pos _ _ hcard] at h
    simpa [he.neg_one_pow] using h
  · rw [ho.neg_one_pow, Module.Ray.neg_units_smul, one_smul,
      Orientation.map_eq_neg_iff_det_neg _ _ hcard] at h
    simpa [ho.neg_one_pow] using h

end LinearEquiv

namespace TauCeti

/-- On `ℂ`, the canonical real orientation is Mathlib's standard orientation, given by the basis
`(1, I)`. -/
theorem reindex_complexOrientation_complex :
    Orientation.reindex ℝ ℂ (finCongr (by simp)) (complexOrientation ℂ) = Complex.orientation := by
  set b : Basis (Fin (finrank ℂ ℂ)) ℂ ℂ :=
    (Basis.singleton (Fin 1) ℂ).reindex (finCongr (finrank_self ℂ).symm)
  rw [b.complexOrientation_eq, ← Basis.orientation_reindex, ← Basis.orientation_reindex,
    Complex.orientation]
  congr 1
  refine Basis.eq_of_apply_eq fun j ↦ ?_
  obtain ⟨⟨i, k⟩, rfl⟩ :=
    ((complexRealIndexEquiv (finrank ℂ ℂ)).trans (finCongr (by simp))).surjective j
  have hi : (i : ℕ) = 0 := by simpa using i.isLt
  have hk : finCongr (by simp) (complexRealIndexEquiv _ (i, k)) = k := Fin.ext (by simp [hi])
  rw [Equiv.trans_apply, Basis.reindex_apply, Equiv.symm_apply_apply, Basis.reindex_apply,
    Equiv.symm_apply_apply, hk]
  simp [b]

/-! ### Products -/

section Prod

-- `Module.Finite ℝ E` follows from the scalar tower, but `Orientation.prod` takes it as an
-- instance argument.
variable {E F : Type*} [AddCommGroup E] [Module ℂ E] [Module ℝ E] [IsScalarTower ℝ ℂ E]
  [FiniteDimensional ℂ E] [Module.Finite ℝ E] [AddCommGroup F] [Module ℂ F] [Module ℝ F]
  [IsScalarTower ℝ ℂ F] [FiniteDimensional ℂ F] [Module.Finite ℝ F]

/-- The ordered product of the canonical orientations of `E` and `F` is the canonical orientation
of `E × F`, after identifying the index types through `finrank ℂ (E × F) = finrank ℂ E +
finrank ℂ F`. -/
theorem prod_complexOrientation :
    (complexOrientation E).prod (complexOrientation F) finrank_real_eq_two_mul_finrank_complex
        finrank_real_eq_two_mul_finrank_complex =
      Orientation.reindex ℝ (E × F) (finCongr (by rw [finrank_prod]; ring))
        (complexOrientation (E × F)) := by
  set b := finBasis ℂ E
  set c := finBasis ℂ F
  set d : Basis (Fin (finrank ℂ (E × F))) ℂ (E × F) :=
    (b.prod c).reindex (finSumFinEquiv.trans (finCongr finrank_prod.symm))
  rw [b.complexOrientation_eq, c.complexOrientation_eq, d.complexOrientation_eq,
    ← Basis.orientation_reindex, ← Basis.orientation_reindex, ← Basis.orientation_reindex,
    ← Basis.orientation_reindex, Orientation.prod_basis_orientation]
  congr 1
  -- Both real bases list `(b₀, 0), (I • b₀, 0), …` and then `(0, c₀), (0, I • c₀), …`.
  refine Basis.eq_of_apply_eq fun j ↦ ?_
  obtain ⟨j | j, rfl⟩ := finSumFinEquiv.surjective j
  · obtain ⟨⟨i, k⟩, rfl⟩ := (complexRealIndexEquiv _).surjective j
    simp only [Basis.reindex_apply, Basis.prod_apply, finCongr_symm, finCongr_apply]
    rw [show (complexRealIndexEquiv _).symm _ = (Fin.cast finrank_prod.symm (Fin.castAdd _ i), k)
      from (Equiv.symm_apply_eq _).2 (Fin.ext (by simp))]
    simp [d]
  · obtain ⟨⟨i, k⟩, rfl⟩ := (complexRealIndexEquiv _).surjective j
    simp only [Basis.reindex_apply, Basis.prod_apply, finCongr_symm, finCongr_apply]
    rw [show (complexRealIndexEquiv _).symm _ = (Fin.cast finrank_prod.symm (Fin.natAdd _ i), k)
      from (Equiv.symm_apply_eq _).2 (Fin.ext (by simp; ring))]
    simp [d]

/-- Exchanging the factors carries the product of the canonical orientations of `E` and `F` to the
product of those of `F` and `E`, with no sign, since both real dimensions are even. -/
theorem map_prodComm_prod_complexOrientation :
    Orientation.map _ (LinearEquiv.prodComm ℝ E F)
        ((complexOrientation E).prod (complexOrientation F) finrank_real_eq_two_mul_finrank_complex
          finrank_real_eq_two_mul_finrank_complex) =
      Orientation.reindex ℝ (F × E) (finCongr (add_comm _ _))
        ((complexOrientation F).prod (complexOrientation E) finrank_real_eq_two_mul_finrank_complex
          finrank_real_eq_two_mul_finrank_complex) :=
  Orientation.map_prodComm_prod_of_even _ _ _ _ ((even_two_mul _).mul_right _)

end Prod

end TauCeti
