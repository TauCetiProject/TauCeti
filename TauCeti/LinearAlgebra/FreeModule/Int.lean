/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import Mathlib.LinearAlgebra.FreeModule.Finite.CardQuotient
public import Mathlib.LinearAlgebra.FreeModule.Finite.Quotient
import Mathlib.GroupTheory.FiniteAbelian.Basic
import Mathlib.LinearAlgebra.Dimension.Localization
-- Proof-only: torsion modules have rank zero.
import Mathlib.LinearAlgebra.Dimension.Torsion.Finite
import TauCeti.Algebra.CharP.Two
import TauCeti.Algebra.Module.Submodule.Quotient

/-!
# Homomorphisms of finitely generated abelian groups

An injective `ℤ`-linear map `f : M → N` into a finitely generated abelian group of the same
rank has image of finite index `c`, so `c • y` lies in the image of `f` for every `y : N`.
Dividing by `f` gives a map `g : N → M` such that `f ∘ g` and `g ∘ f` are both multiplication by
`c`: an inverse of `f` up to a nonzero scalar. Over `ℚ` the map `f` becomes invertible with
inverse `c⁻¹ • g`; over `ℤ` an inverse up to a scalar is the best available.

The index of the image of a `ℤ`-linear map between free abelian groups is the absolute value of
the determinant of `f` in any bases of `M` and `N` indexed by the same finite type; a
non-injective `f` has image of infinite index (index `0`) and determinant `0`.

A homomorphism from a free abelian group of finite rank `r` is determined freely by its values on
a basis, so there are `|A| ^ r` homomorphisms to an abelian group `A`. In particular a free
abelian group of rank two has exactly four homomorphisms to `ℤ/2`: given a nonzero `ι` and any
`χ` other than `0` and `ι`, they are `0`, `ι`, `χ` and `χ + ι`.

## Main results

* `LinearMap.exists_comp_eq_nsmul_id_of_injective`: an injective map between finitely generated
  abelian groups of equal rank has an inverse up to multiplication by a nonzero natural
  number.
* `LinearMap.index_range_eq_natAbs_det_toMatrix`: for any `ℤ`-linear map between free abelian
  groups with bases indexed by the same finite type, the index of the image is the absolute value
  of the determinant of its matrix.
* `Module.Basis.card_quotient_span_range_nsmul`: rescaling the vectors of a finite integral basis
  by natural numbers `m k`, the quotient by the span of the `m k • b k` has `Nat.card` equal to
  `∏ k, m k`.
* `LinearIndependent.card_quotient_span_range_nsmul`: rescaling a finite linearly independent
  family `v` by natural numbers `m k` multiplies the `Nat.card` of the quotient by its span by
  `∏ k, m k`; both sides are `0` when one of the quotients is infinite.
* `TauCeti.natCard_addMonoidHom_eq_pow_finrank`: a free abelian group of finite rank `r` has
  `Nat.card A ^ r` homomorphisms to `A`; they are finite in number when `A` is finite
  (`TauCeti.finite_addMonoidHom`).
* `TauCeti.nodup_addMonoidHom_zmod_two`: for a nonzero `ι : G →+ ℤ/2` and a `χ` other than `0`
  and `ι`, the homomorphisms `0`, `ι`, `χ` and `χ + ι` are pairwise distinct.
* `TauCeti.univ_addMonoidHom_zmod_two_eq_of_finrank_eq_two`,
  `TauCeti.addMonoidHom_zmod_two_eq_zero_or_eq_or_eq_or_eq_add_of_finrank_eq_two`: a free abelian
  group of rank two has four homomorphisms to `ℤ/2`, namely `0`, `ι`, `χ` and `χ + ι` for any
  nonzero `ι` and any `χ` other than `0` and `ι`.
-/

public section

namespace LinearMap

variable {M N : Type*} [AddCommGroup M] [AddCommGroup N]

/-- An injective `ℤ`-linear map into a finitely generated abelian group of the same rank
has an inverse up to multiplication by a nonzero natural number `c`. -/
theorem exists_comp_eq_nsmul_id_of_injective [Module.Finite ℤ N] {f : M →ₗ[ℤ] N}
    (hf : Function.Injective f) (hrank : Module.finrank ℤ M = Module.finrank ℤ N) :
    ∃ c : ℕ, c ≠ 0 ∧ ∃ g : N →ₗ[ℤ] M, f ∘ₗ g = c • LinearMap.id ∧ g ∘ₗ f = c • LinearMap.id := by
  have : Finite (N ⧸ range f) := by
    have hq := (range f).finrank_quotient_add_finrank
    rw [(finrank_range_of_inj hf).trans hrank] at hq
    have hq0 : Module.finrank ℤ (N ⧸ range f) = 0 := by lia
    exact Module.finite_of_fg_torsion _ (Module.finrank_eq_zero_iff_isTorsion.mp hq0)
  have : Finite (N ⧸ (range f).toAddSubgroup) := ‹Finite (N ⧸ range f)›
  set c := (range f).toAddSubgroup.index
  let g : N →ₗ[ℤ] M := (LinearEquiv.ofInjective f hf).symm.toLinearMap ∘ₗ
    (c • LinearMap.id).codRestrict (range f) fun y ↦ (range f).toAddSubgroup.nsmul_index_mem y
  have hfg : f ∘ₗ g = c • LinearMap.id := by
    ext y
    simp [g]
  refine ⟨c, AddSubgroup.index_ne_zero_of_finite, g, hfg, ?_⟩
  ext x
  apply hf
  simpa using congr($hfg (f x))

/-- **The index of the image of a map is the absolute value of its determinant**: for bases `b` of
`M` and `c` of `N` indexed by the same finite type, the image of a `ℤ`-linear map `f : M → N` has
index `|det (toMatrix b c f)|`. A non-injective `f` has image of infinite index, hence index `0`,
and determinant `0`. -/
theorem index_range_eq_natAbs_det_toMatrix {ι : Type*} [Fintype ι] [DecidableEq ι]
    (b : Module.Basis ι ℤ M) (c : Module.Basis ι ℤ N) (f : M →ₗ[ℤ] N) :
    (range f).toAddSubgroup.index = (toMatrix b c f).det.natAbs := by
  by_cases hf : Function.Injective f
  swap
  · -- a non-injective map has vanishing determinant and image of infinite index
    obtain ⟨v, hv, hv0⟩ := (ker f).ne_bot_iff.mp (mt ker_eq_bot.mp hf)
    have hdet : (toMatrix b c f).det = 0 := by
      rw [← Matrix.exists_mulVec_eq_zero_iff]
      refine ⟨fun i ↦ b.repr v i, by simpa, ?_⟩
      simpa [toMatrix_mulVec_repr] using hv
    rw [hdet, Int.natAbs_zero, AddSubgroup.index_eq_zero_iff_infinite]
    refine not_finite_iff_infinite.mp fun h ↦ ?_
    have := Module.Finite.of_basis b
    have := Module.Finite.of_basis c
    have := Module.Free.of_basis c
    have := Module.Free.of_basis b
    have h1 := (Submodule.finiteQuotient_iff (range f)).mp h
    have h2 := (ker f).finrank_quotient_add_finrank
    rw [f.quotKerEquivRange.finrank_eq] at h2
    have h3 : 0 < Module.finrank ℤ (ker f) :=
      Module.finrank_pos_iff_exists_ne_zero.mpr ⟨⟨v, hv⟩, by simpa using hv0⟩
    rw [h1, Module.finrank_eq_card_basis b, Module.finrank_eq_card_basis c] at h2
    lia
  rw [AddSubgroup.index_eq_natAbs_det c (range f).toAddSubgroup
    (b.map (LinearEquiv.ofInjective f hf)), Module.Basis.det_apply]
  congr 2
  ext i j
  simp only [toMatrix_apply, Module.Basis.toMatrix_apply, Module.Basis.map_apply]
  -- the `j`-th basis vector of the image is `f (b j)`, coerced through `AddSubgroup`
  exact congr(c.repr $(LinearEquiv.ofInjective_apply f (h := hf) (b j)) i)

end LinearMap

/-! ### Rescaled bases -/

namespace Module.Basis

variable {κ M : Type*} [AddCommGroup M] (b : Basis κ ℤ M) (m : κ → ℕ)

/-- The quotient of `M` by the span of the rescaled basis vectors `m k • b k` has `Nat.card` equal
to `∏ k, m k`. When some `m k` vanishes the quotient is infinite and both sides are `0`. -/
theorem card_quotient_span_range_nsmul [Fintype κ] :
    Nat.card (M ⧸ Submodule.span ℤ (Set.range fun k ↦ m k • b k)) = ∏ k, m k := by
  simp_rw [← natCast_zsmul]
  rw [Nat.card_congr (b.quotientSpanSMulEquiv fun k ↦ (m k : ℤ)).toEquiv, Nat.card_pi]
  simp [Nat.card_congr (Int.quotientSpanNatEquivZMod _).toEquiv]

end Module.Basis

/-- **Rescaling a linearly independent family.** Rescaling a finite linearly independent family
`v` in an abelian group by natural numbers `m k` multiplies the `Nat.card` of the quotient by its
span by `∏ k, m k`. Both sides are `0` when one of the quotients is infinite. -/
theorem LinearIndependent.card_quotient_span_range_nsmul {κ M : Type*} [AddCommGroup M]
    [Fintype κ] {v : κ → M} (hv : LinearIndependent ℤ v) (m : κ → ℕ) :
    Nat.card (M ⧸ Submodule.span ℤ (Set.range fun k ↦ m k • v k)) =
      (∏ k, m k) * Nat.card (M ⧸ Submodule.span ℤ (Set.range v)) := by
  set Q := Submodule.span ℤ (Set.range v)
  set P := Submodule.span ℤ (Set.range fun k ↦ m k • v k)
  have hPQ : P ≤ Q := Submodule.span_le.2 <| by
    rintro _ ⟨k, rfl⟩
    exact Submodule.smul_of_tower_mem _ _ (Submodule.subset_span ⟨k, rfl⟩)
  -- In the basis `b` of `Q` given by `v`, `P` is the span of the rescaled basis vectors.
  let b := Module.Basis.span hv
  have hcomap : P.comap Q.subtype = Submodule.span ℤ (Set.range fun k ↦ m k • b k) := by
    rw [← Submodule.comap_map_eq_of_injective Q.injective_subtype
      (Submodule.span ℤ (Set.range fun k ↦ m k • b k)), Submodule.map_span, ← Set.range_comp]
    have hb : (Q.subtype ∘ fun k ↦ m k • b k) = fun k ↦ m k • v k := by
      ext k
      simp [b, Module.Basis.span_apply]
    rw [hb]
  -- The quotient of `Q` by `P` is the image of `Q` in `M ⧸ P`, by the first isomorphism theorem.
  have hker : LinearMap.ker (P.mkQ ∘ₗ Q.subtype) = P.comap Q.subtype := by
    rw [LinearMap.ker_comp, Submodule.ker_mkQ]
  have hrange : LinearMap.range (P.mkQ ∘ₗ Q.subtype) = Q.map P.mkQ := by
    rw [LinearMap.range_comp, Submodule.range_subtype]
  rw [← Submodule.card_quotient_mul_card_quotient Q P hPQ, ← b.card_quotient_span_range_nsmul m,
    ← hcomap]
  congr 1
  exact Nat.card_congr ((Submodule.quotEquivOfEq _ _ hker.symm).trans
    ((P.mkQ ∘ₗ Q.subtype).quotKerEquivRange.trans (LinearEquiv.ofEq _ _ hrange))).toEquiv.symm

namespace TauCeti

/-- A free abelian group of finite rank `r` has `Nat.card A ^ r` additive homomorphisms to an
abelian group `A`, one for each choice of values on a basis. -/
theorem natCard_addMonoidHom_eq_pow_finrank (M A : Type*) [AddCommGroup M] [AddCommGroup A]
    [Module.Free ℤ M] [Module.Finite ℤ M] :
    Nat.card (M →+ A) = Nat.card A ^ Module.finrank ℤ M := by
  rw [Nat.card_congr ((addMonoidHomLequivInt ℤ).toEquiv.trans
    ((Module.finBasis ℤ M).constr ℤ).symm.toEquiv), Nat.card_fun, Nat.card_fin]

/-- A free abelian group of finite rank has finitely many homomorphisms to a finite abelian
group. -/
instance finite_addMonoidHom (M A : Type*) [AddCommGroup M] [AddCommGroup A] [Module.Free ℤ M]
    [Module.Finite ℤ M] [Finite A] : Finite (M →+ A) :=
  Nat.finite_of_card_ne_zero <| by
    rw [natCard_addMonoidHom_eq_pow_finrank]
    exact pow_ne_zero _ Nat.card_pos.ne'

/-- For a nonzero homomorphism `ι` to `ℤ/2` and a `χ` other than `0` and `ι`, the homomorphisms
`0`, `ι`, `χ` and `χ + ι` are pairwise distinct. -/
theorem nodup_addMonoidHom_zmod_two {G : Type*} [AddCommGroup G] {ι χ : G →+ ZMod 2}
    (hι : ι ≠ 0) (hχ₀ : χ ≠ 0) (hχι : χ ≠ ι) : [0, ι, χ, χ + ι].Nodup := by
  simp [add_eq_zero_iff_eq_of_charTwo (ZMod 2), hι, hχ₀, hχι, hχι.symm,
    eq_comm (a := (0 : G →+ ZMod 2))]

section RankTwo

variable {Λ : Type*} [AddCommGroup Λ] [Module.Free ℤ Λ] [Module.Finite ℤ Λ]

/-- A lattice of rank two, such as `H₁` of a torus, has four homomorphisms to `ℤ/2`. -/
theorem natCard_addMonoidHom_zmod_two_of_finrank_eq_two (h : Module.finrank ℤ Λ = 2) :
    Nat.card (Λ →+ ZMod 2) = 4 := by
  rw [natCard_addMonoidHom_eq_pow_finrank, h, Nat.card_zmod]
  norm_num

/-- On a lattice of rank two, the homomorphisms to `ℤ/2` are `0`, `ι`, `χ` and `χ + ι` for a
nonzero `ι` and a `χ` other than `0` and `ι`. -/
theorem univ_addMonoidHom_zmod_two_eq_of_finrank_eq_two [Fintype (Λ →+ ZMod 2)]
    [DecidableEq (Λ →+ ZMod 2)] (h : Module.finrank ℤ Λ = 2) {ι χ : Λ →+ ZMod 2} (hι : ι ≠ 0)
    (hχ₀ : χ ≠ 0) (hχι : χ ≠ ι) :
    (Finset.univ : Finset (Λ →+ ZMod 2)) = {0, ι, χ, χ + ι} := by
  refine (Finset.eq_univ_of_card _ ?_).symm
  rw [← Nat.card_eq_fintype_card, natCard_addMonoidHom_zmod_two_of_finrank_eq_two h]
  simpa using List.toFinset_card_of_nodup (nodup_addMonoidHom_zmod_two hι hχ₀ hχι)

/-- On a lattice of rank two, if `ι` is a nonzero homomorphism to `ℤ/2` and `χ` is neither `0`
nor `ι`, every homomorphism to `ℤ/2` is `0`, `ι`, `χ` or `χ + ι`. -/
theorem addMonoidHom_zmod_two_eq_zero_or_eq_or_eq_or_eq_add_of_finrank_eq_two
    (h : Module.finrank ℤ Λ = 2) {ι χ : Λ →+ ZMod 2} (hι : ι ≠ 0) (hχ₀ : χ ≠ 0) (hχι : χ ≠ ι)
    (ψ : Λ →+ ZMod 2) : ψ = 0 ∨ ψ = ι ∨ ψ = χ ∨ ψ = χ + ι := by
  classical
  let _ := Fintype.ofFinite (Λ →+ ZMod 2)
  simpa [univ_addMonoidHom_zmod_two_eq_of_finrank_eq_two h hι hχ₀ hχι] using Finset.mem_univ ψ

end RankTwo

end TauCeti
