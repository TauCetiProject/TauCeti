/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import Mathlib.RingTheory.RootsOfUnity.Basic
public import TauCeti.Algebra.AlgebraicGroup.MultiplicativeGroup.WeilRestriction.Basic
public import TauCeti.RingTheory.Norm.Units
public import TauCeti.RingTheory.NormTrace.BaseChange

/-!
# Norm maps and norm-one tori

Let `k'` be a commutative `k`-algebra that is free of finite rank `d` as a `k`-module. The points of
the Weil restriction `Res_{k'/k} 𝔾ₘ` over a commutative `k`-algebra `R` are the units of
`k' ⊗[k] R` (`TauCeti.Algebra.WeilRestriction.multiplicativeGroupPoints`). The norm of the free
`R`-algebra `R ⊗[k] k'` of rank `d` gives a homomorphism `Nm : (k' ⊗[k] R)ˣ →* Rˣ`, natural in `R`:
this is the norm morphism `Res_{k'/k} 𝔾ₘ → 𝔾ₘ` on points. Its kernel is the group of points of
the norm kernel `R_{k'/k}^1 𝔾ₘ`; when `k'/k` is a finite separable field extension (more generally,
`k'` is finite étale and free over `k`) this is the norm-one torus, but in general it need not be
a torus: for `k' = k[ε]/(ε²)` over a field `k` of characteristic zero it contains a copy
`a ↦ 1 + aε` of the additive group `𝔾ₐ`. For `ℂ/ℝ` on real points the norm is `z ↦ z * conj z`.

This file defines the norm on points and its kernel, computes the norm on the diagonal
`Rˣ → (k' ⊗[k] R)ˣ` and on the units of `k'`, and proves its naturality in `R`. By the Yoneda
lemma, the norm of the universal point of `Res_{k'/k} 𝔾ₘ` is the coordinate algebra map
`TauCeti.NormTorus.normHom` of the norm morphism, which induces the norm on points of every
`k`-algebra. The file also defines the image `μ_n(R) → μ_n(k' ⊗[k] R)` of the roots of unity
along the diagonal, whose quotient is the abstract group `μ_n(k' ⊗[k] R) / μ_n(R)`.

## Main definitions

* `TauCeti.NormTorus.norm k k' R`: the norm `(k' ⊗[k] R)ˣ →* Rˣ`, the algebra norm of
  `R ⊗[k] k'` over `R` after commuting the tensor factors.
* `TauCeti.NormTorus.normOne k k' R`: its kernel; for `k'` free of finite rank over `k`, the points
  over `R` of the norm kernel, which is the norm-one torus when `k'/k` is finite separable.
* `TauCeti.NormTorus.normHom k k'`: the norm morphism `Res_{k'/k} 𝔾ₘ → 𝔾ₘ`, as a `k`-algebra map
  of coordinate algebras.
* `TauCeti.NormTorus.diagonalRootsOfUnity k k' R n`: the image of `μ_n(R)` in `μ_n(k' ⊗[k] R)`.

## Main results

* `TauCeti.NormTorus.norm_unitsMap_includeRight`: `Nm(1 ⊗ r) = r ^ d`.
* `TauCeti.NormTorus.norm_unitsMap_includeLeft`: on `a ⊗ 1` with `a ∈ k'ˣ`, the norm is the norm of
  `a` over `k`.
* `TauCeti.NormTorus.norm_eq_normUnits`: on `k`-points, the norm is the norm of `k'` over `k`.
* `TauCeti.NormTorus.norm_unitsMap_lTensor`: the norm is natural in the coefficient algebra `R`.
* `TauCeti.NormTorus.norm_self`: for the trivial extension `k' = k` the norm is the identity, so
  the norm kernel is trivial (`TauCeti.NormTorus.normOne_self`).
* `TauCeti.NormTorus.pointsMulEquiv_comp_normHom`: on points, `normHom` induces `norm`.

## References

* F. Bruhat, J. Tits, *Groupes réductifs sur un corps local. II*, Publ. Math. IHÉS 60 (1984),
  1.5.13 and 1.5.17.
* T. Kaletha, *Supercuspidal L-packets*, §3.1, for `μ_n(k' ⊗[k] R) / μ_n(R)`.
-/

public section

open WithConv
open scoped TensorProduct LaurentPolynomial

namespace TauCeti.NormTorus

variable (k k' R : Type*) [CommRing k] [CommRing k'] [Algebra k k'] [CommRing R] [Algebra k R]

/-- **The norm on points of `Res_{k'/k} 𝔾ₘ`.** For a commutative `k`-algebra `R`, the homomorphism
`(k' ⊗[k] R)ˣ →* Rˣ` given by the algebra norm of `R ⊗[k] k'` over `R`, after commuting the tensor
factors. When `k'` is free of rank `d` over `k`, the `R`-algebra `R ⊗[k] k'` is free of rank `d`, so
this is a determinant of size `d`; otherwise `Algebra.norm` is `1` on modules without a finite
basis. -/
noncomputable def norm : (k' ⊗[k] R)ˣ →* Rˣ :=
  (Algebra.normUnits R).comp
    (Units.map (Algebra.TensorProduct.comm k k' R : k' ⊗[k] R →* R ⊗[k] k'))

variable {k k' R}

/-- The value of `TauCeti.NormTorus.norm` is the algebra norm over `R` of the unit, read in
`R ⊗[k] k'`. -/
@[simp]
theorem coe_norm (u : (k' ⊗[k] R)ˣ) :
    (norm k k' R u : R) = Algebra.norm R (Algebra.TensorProduct.comm k k' R u) := by
  simp [norm]

/-- **The norm of the diagonal.** For `k'` free of rank `d` over `k`, the norm of the image
`1 ⊗ r` of a unit `r` of `R` is `r ^ d`. Geometrically, the composite of the diagonal
`𝔾ₘ → Res_{k'/k} 𝔾ₘ` with the norm is the `d`-th power map. -/
@[simp]
theorem norm_unitsMap_includeRight [Module.Free k k'] (r : Rˣ) :
    norm k k' R (Units.map (Algebra.TensorProduct.includeRight : R →ₐ[k] k' ⊗[k] R) r) =
      r ^ Module.finrank k k' := by
  nontriviality R
  have : Nontrivial k := (algebraMap k R).domain_nontrivial
  ext
  -- after commuting the factors, `1 ⊗ r` is the scalar `r` of the free `R`-algebra `R ⊗[k] k'`
  rw [coe_norm, Units.coe_map, MonoidHom.coe_ofClass, Algebra.TensorProduct.includeRight_apply,
    Algebra.TensorProduct.comm_tmul,
    show (r : R) ⊗ₜ[k] (1 : k') = algebraMap R (R ⊗[k] k') r by simp, Algebra.norm_algebraMap,
    Module.finrank_baseChange, Units.val_pow_eq_pow_val]

variable (R) in
/-- **The norm of a unit of `k'`.** For `k'` free of finite rank over `k`, the norm of the image
`a ⊗ 1` of a unit `a` of `k'` is the image in `R` of the norm of `a` over `k`. -/
@[simp]
theorem norm_unitsMap_includeLeft [Module.Free k k'] [Module.Finite k k'] (a : k'ˣ) :
    norm k k' R (Units.map (Algebra.TensorProduct.includeLeft : k' →ₐ[k] k' ⊗[k] R) a) =
      Units.map (algebraMap k R : k →* R) (Algebra.normUnits k a) := by
  ext
  simp

/-- **The norm on rational points.** Over `R = k`, through `k' ⊗[k] k ≃ k'`, the norm is the norm
of `k'` over `k`. -/
theorem norm_eq_normUnits (u : (k' ⊗[k] k)ˣ) :
    norm k k' k u =
      Algebra.normUnits k (Units.map (Algebra.TensorProduct.rid k k k' : k' ⊗[k] k →* k') u) := by
  ext
  -- read `k ⊗[k] k'` as `k'` through `lid`, along which `comm` becomes `rid`
  rw [coe_norm, ← Algebra.norm_eq_of_algEquiv (Algebra.TensorProduct.lid k k'),
    Algebra.coe_normUnits, Units.coe_map, MonoidHom.coe_ofClass]
  exact congrArg _ (TensorProduct.lid_comm (R := k) (M := k') _)

/-- **Naturality of the norm.** For `k'` free of finite rank over `k` and a `k`-algebra map
`h : R →ₐ[k] R'`, applying `k' ⊗ h` and then the norm over `R'` is applying the norm over `R` and
then `h`. -/
theorem norm_unitsMap_lTensor [Module.Free k k'] [Module.Finite k k'] {R' : Type*} [CommRing R']
    [Algebra k R'] (h : R →ₐ[k] R') (u : (k' ⊗[k] R)ˣ) :
    norm k k' R' (Units.map (Algebra.TensorProduct.lTensor (S := k') k' h : k' ⊗[k] R →* k' ⊗[k] R')
        u) = Units.map (h : R →* R') (norm k k' R u) := by
  ext
  -- after commuting the factors, `k' ⊗ h` becomes `h ⊗ k'`, along which the norm is natural
  rw [coe_norm, Units.coe_map, MonoidHom.coe_ofClass,
    show Algebra.TensorProduct.lTensor (S := k') k' h (u : k' ⊗[k] R) =
      Algebra.TensorProduct.map (AlgHom.id k k') h u from rfl,
    Algebra.TensorProduct.comm_comp_map_apply, Algebra.norm_rTensor]
  simp

/-- **The norm for the trivial extension.** For `k' = k`, the norm on `(k ⊗[k] R)ˣ` is the
identification `k ⊗[k] R ≃ R`. -/
@[simp]
theorem norm_self (u : (k ⊗[k] R)ˣ) :
    norm k k R u = Units.map (Algebra.TensorProduct.lid k R : k ⊗[k] R →* R) u := by
  ext
  -- read `R ⊗[k] k` as `R` through `rid`, along which `comm` becomes `lid`
  rw [coe_norm, ← Algebra.norm_eq_of_algEquiv (Algebra.TensorProduct.rid k R R),
    Algebra.norm_self, MonoidHom.id_apply, Units.coe_map, MonoidHom.coe_ofClass]
  exact TensorProduct.rid_comm (R := k) (M := R) _

section NormOne

variable (k k' R)

/-- **The points of the norm kernel.** The kernel of the norm `(k' ⊗[k] R)ˣ →* Rˣ`. When `k'` is
free of finite rank over `k`, this is the group of points over `R` of the kernel `R_{k'/k}^1 𝔾ₘ` of
the norm morphism; if moreover `k'/k` is a finite separable field extension (or `k'` is finite
étale over `k`) this is the norm-one torus, but in general it need not be a torus. -/
noncomputable def normOne : Subgroup (k' ⊗[k] R)ˣ :=
  (norm k k' R).ker

variable {k k' R}

@[simp]
theorem mem_normOne {u : (k' ⊗[k] R)ˣ} : u ∈ normOne k k' R ↔ norm k k' R u = 1 :=
  MonoidHom.mem_ker

/-- The norm-one subgroups are functorial in the coefficient algebra: a `k`-algebra map
`h : R →ₐ[k] R'` carries points of norm one over `R` to points of norm one over `R'`. -/
theorem unitsMap_lTensor_mem_normOne [Module.Free k k'] [Module.Finite k k'] {R' : Type*}
    [CommRing R'] [Algebra k R'] (h : R →ₐ[k] R') {u : (k' ⊗[k] R)ˣ} (hu : u ∈ normOne k k' R) :
    Units.map (Algebra.TensorProduct.lTensor (S := k') k' h : k' ⊗[k] R →* k' ⊗[k] R') u ∈
      normOne k k' R' := by
  rw [mem_normOne] at hu ⊢
  rw [norm_unitsMap_lTensor, hu, map_one]

/-- For `k'` free of rank `d` over `k`, a unit `r` of `R` lies in the norm kernel through the
diagonal `r ↦ 1 ⊗ r` exactly when `r ^ d = 1`. -/
theorem unitsMap_includeRight_mem_normOne_iff [Module.Free k k'] {r : Rˣ} :
    Units.map (Algebra.TensorProduct.includeRight : R →ₐ[k] k' ⊗[k] R) r ∈ normOne k k' R ↔
      r ^ Module.finrank k k' = 1 := by
  rw [mem_normOne, norm_unitsMap_includeRight]

variable (k R) in
/-- For the trivial extension `k' = k` the norm kernel is trivial. -/
@[simp]
theorem normOne_self : normOne k k R = ⊥ := by
  refine (Subgroup.eq_bot_iff_forall _).2 fun u hu ↦ ?_
  rw [mem_normOne, norm_self] at hu
  exact Units.map_injective (Algebra.TensorProduct.lid k R).injective (hu.trans (map_one _).symm)

end NormOne

section NormHom

variable (k k') [Module.Free k k'] [Module.Finite k k']

/-- **The norm morphism `Res_{k'/k} 𝔾ₘ → 𝔾ₘ`**, as the map `k[T;T⁻¹] →ₐ[k] Res_{k'/k} k'[T;T⁻¹]`
of coordinate algebras. It sends the coordinate `T` of `𝔾ₘ` to the norm of the universal point of
`Res_{k'/k} 𝔾ₘ`; on points over every `k`-algebra it induces `TauCeti.NormTorus.norm`, see
`TauCeti.NormTorus.pointsMulEquiv_comp_normHom`. -/
noncomputable def normHom : k[T;T⁻¹] →ₐ[k] Algebra.WeilRestriction k k' k'[T;T⁻¹] :=
  laurentEval <| norm k k' _ <| Algebra.WeilRestriction.multiplicativeGroupPoints k k' _ <|
    toConv (AlgHom.id k _)

variable {k k'}

/-- **The norm morphism on points.** For a point `f` of `Res_{k'/k} 𝔾ₘ` over a commutative
`k`-algebra `R`, the point `f ∘ normHom` of `𝔾ₘ` is the norm of the unit of `k' ⊗[k] R`
attached to `f`. -/
theorem pointsMulEquiv_comp_normHom
    (f : WithConv (Algebra.WeilRestriction k k' k'[T;T⁻¹] →ₐ[k] R)) :
    MultiplicativeGroup.pointsMulEquiv (toConv (f.ofConv.comp (normHom k k'))) =
      norm k k' R (Algebra.WeilRestriction.multiplicativeGroupPoints k k' R f) := by
  -- `f` is the image of the universal point under `f`, so this is the naturality of the norm
  have hf : f = toConv (f.ofConv.comp (AlgHom.id k _)) := by rw [AlgHom.comp_id, toConv_ofConv]
  rw [normHom, ← AlgHom.mapValue_apply, ← MultiplicativeGroup.pointsMulEquiv_symm_apply,
    MultiplicativeGroup.pointsMulEquiv_mapValue, MulEquiv.apply_symm_apply, ← norm_unitsMap_lTensor,
    ← Algebra.WeilRestriction.multiplicativeGroupPoints_naturality, ← hf]

end NormHom

section RootsOfUnity

variable (k k' R)

/-- **The diagonal roots of unity.** The image of `μ_n(R)` in `μ_n(k' ⊗[k] R)` under the diagonal
`r ↦ 1 ⊗ r`. The quotient `rootsOfUnity n (k' ⊗[k] R) ⧸ diagonalRootsOfUnity k k' R n` is the
abstract group `μ_n(k' ⊗[k] R) / μ_n(R)`. -/
noncomputable def diagonalRootsOfUnity (n : ℕ) : Subgroup (rootsOfUnity n (k' ⊗[k] R)) :=
  (restrictRootsOfUnity (Algebra.TensorProduct.includeRight : R →ₐ[k] k' ⊗[k] R) n).range

variable {k k' R}

theorem mem_diagonalRootsOfUnity {n : ℕ} {ζ : rootsOfUnity n (k' ⊗[k] R)} :
    ζ ∈ diagonalRootsOfUnity k k' R n ↔ ∃ r : rootsOfUnity n R,
      Units.map (Algebra.TensorProduct.includeRight : R →ₐ[k] k' ⊗[k] R) (r : Rˣ) =
        (ζ : (k' ⊗[k] R)ˣ) := by
  refine MonoidHom.mem_range.trans (exists_congr fun r ↦ ?_)
  rw [Subtype.ext_iff, Units.ext_iff, Units.ext_iff]
  simp only [restrictRootsOfUnity_coe_apply, Units.coe_map, MonoidHom.coe_ofClass]

variable (k R) in
/-- For the trivial extension `k' = k`, every root of unity of `k ⊗[k] R` is diagonal. -/
@[simp]
theorem diagonalRootsOfUnity_self (n : ℕ) : diagonalRootsOfUnity k k R n = ⊤ := by
  refine (Subgroup.eq_top_iff' _).2 fun ζ ↦ mem_diagonalRootsOfUnity.2 ?_
  -- `1 ⊗ r ↦ r` is inverse to the diagonal, so `ζ` is the diagonal image of its image in `R`
  refine ⟨restrictRootsOfUnity (Algebra.TensorProduct.lid k R) n ζ, Units.ext ?_⟩
  simp only [Units.coe_map, MonoidHom.coe_ofClass, restrictRootsOfUnity_coe_apply,
    Algebra.TensorProduct.includeRight_apply]
  rw [← Algebra.TensorProduct.lid_symm_apply]
  exact (Algebra.TensorProduct.lid k R).symm_apply_apply _

end RootsOfUnity

end TauCeti.NormTorus
