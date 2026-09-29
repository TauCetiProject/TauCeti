/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.Algebra.CrossedProduct.Basic
public import Mathlib.LinearAlgebra.Matrix.GeneralLinearGroup.Defs
public import Mathlib.RingTheory.TensorProduct.Maps
-- Non-public: Skolem–Noether (`TauCeti.exists_unit_conj_of_algEquiv`) at the central simple algebra
-- `Mₙ(L)`, whose centrality and simplicity come from the two Mathlib matrix instances, and the
-- uniqueness of conjugators up to scalars, are used only in proofs.
import TauCeti.Algebra.CentralSimple.SkolemNoether
import TauCeti.LinearAlgebra.Matrix.GeneralLinearGroup.Conjugation
import Mathlib.Algebra.Central.Basic
import Mathlib.Algebra.Central.Matrix
import Mathlib.RingTheory.SimpleRing.Matrix

/-!
# The Galois `2`-cocycle of a split algebra

Let `A` be a `K`-algebra and `L` a field equipped with a `K`-algebra structure, and suppose we are
given descent data in the form of an `L`-algebra isomorphism `φ : L ⊗[K] A ≃ₐ[L] Mₙ(L)`. This file
attaches to `φ` a `2`-cocycle of `Aut_K(L)` with values in `Lˣ`, in the normalization of
`TauCeti.TwoCocycle`.

Each `σ : L ≃ₐ[K] L` acts on `L ⊗[K] A` by `σ ⊗ 1` and on `Mₙ(L)` entrywise, and both actions are
`σ`-semilinear. Transporting `σ ⊗ 1` along `φ` and undoing the entrywise action gives the
automorphism
`splittingAut φ σ = φ ∘ (σ ⊗ 1) ∘ φ⁻¹ ∘ σ⁻¹`
of `Mₙ(L)`, which is `L`-linear. By Skolem–Noether (`TauCeti.exists_unit_conj_of_algEquiv`) it is
conjugation by some `g_σ ∈ GL_n(L)`, determined up to `Lˣ`. The automorphisms satisfy
`splittingAut φ (στ) = splittingAut φ σ ∘ σ ∘ splittingAut φ τ ∘ σ⁻¹`, so `g_στ` and `g_σ · σ(g_τ)`
induce the same conjugation and differ by a unit scalar; this scalar is the cocycle:
`c(σ, τ) · g_σ · σ(g_τ) = g_στ`.

The construction is carried out for an arbitrary family of conjugators in
`TauCeti.TwoCocycle.ofConjugators`, since the cocycle depends on the conjugators and not only on
`φ`; `TauCeti.cocycleOfSplitting` is the cocycle of the conjugators chosen by
`TauCeti.splittingConjugator`. Only the choice of conjugators, via Skolem–Noether, needs `L` to be
a field: `splittingAut` and its lemmas are stated for a commutative semiring `L`, and
`TauCeti.TwoCocycle.ofConjugators` for a commutative ring `L`.

## Main definitions

* `TauCeti.splittingAut φ σ`: the `L`-algebra automorphism `φ ∘ (σ ⊗ 1) ∘ φ⁻¹ ∘ σ⁻¹` of `Mₙ(L)`.
* `TauCeti.splittingConjugator φ σ`: a chosen `g_σ ∈ GL_n(L)` with `splittingAut φ σ` equal to
  conjugation by `g_σ`.
* `TauCeti.TwoCocycle.ofConjugators φ g hg`: the `2`-cocycle of a family `g` of conjugators, the
  unit scalars `c(σ, τ)` with `c(σ, τ) · g_σ · σ(g_τ) = g_στ`.
* `TauCeti.cocycleOfSplitting φ`: the cocycle of the chosen conjugators.

## Main results

* `TauCeti.splittingAut_mul`: the twisted multiplicativity of `σ ↦ splittingAut φ σ`.
* `TauCeti.TwoCocycle.ofConjugators_toFun_eq_iff`: the value `c(σ, τ)` is the unique unit `u` with
  `u · g_σ · σ(g_τ) = g_στ`.
* `TauCeti.cocycleOfSplitting_toFun_eq_iff`: the same characterization of `cocycleOfSplitting φ`
  with respect to the chosen conjugators `splittingConjugator φ σ`.

## Implementation notes

The sign of the cocycle is chosen with the crossed product in mind: for the crossed product
`A = (L, Aut_K(L), c)`, split by `a ⊗ x ↦ (v ↦ a · v · x)` into the `L`-linear endomorphisms of
`A` as a right `L`-vector space with basis `u_σ`, the conjugators satisfy
`c(σ, τ) · g_σ · σ(g_τ) = g_στ` for the defining cocycle `c`. The connecting map of
`1 → Lˣ → GL_n(L) → PGL_n(L) → 1`, which reads `g_σ · σ(g_τ) = δ(σ, τ) · g_στ`, is the inverse
cocycle and presents the opposite algebra.

## References

* P. Gille and T. Szamuely, *Central Simple Algebras and Galois Cohomology* (2006), Ch. 2 and §4.4.
* J.-P. Serre, *Local Fields*, GTM 67 (1979), Chapter X.
-/

public section

open scoped TensorProduct

open Matrix Matrix.GeneralLinearGroup

universe u v w

namespace TauCeti

variable {K : Type u} [CommSemiring K] {A : Type w} [Semiring A] [Algebra K A]
  {n : Type*} [Fintype n] [DecidableEq n]

section CommSemiring

variable {L : Type v} [CommSemiring L] [Algebra K L]

/-- The automorphism `φ ∘ (σ ⊗ 1) ∘ φ⁻¹ ∘ σ⁻¹` of `Mₙ(L)` attached to a splitting
`φ : L ⊗[K] A ≃ₐ[L] Mₙ(L)` and `σ : L ≃ₐ[K] L`, where `σ⁻¹` acts on matrices entrywise. The two
semilinear twists cancel, so it is an automorphism of `L`-algebras. -/
noncomputable def splittingAut (φ : L ⊗[K] A ≃ₐ[L] Matrix n n L) (σ : L ≃ₐ[K] L) :
    Matrix n n L ≃ₐ[L] Matrix n n L :=
  AlgEquiv.ofRingEquiv (f := (σ.symm.mapMatrix.trans ((φ.restrictScalars K).symm.trans
      ((Algebra.TensorProduct.congr σ .refl).trans (φ.restrictScalars K)))).toRingEquiv)
    fun x ↦ by
      -- the entrywise action of `σ⁻¹` sends the scalar matrix of `x` to that of `σ⁻¹ x`
      have hx : σ.symm.mapMatrix (algebraMap L (Matrix n n L) x) =
          algebraMap L (Matrix n n L) (σ.symm x) := by
        ext i j
        simp only [AlgEquiv.mapMatrix_apply, Matrix.map_apply, Matrix.algebraMap_matrix_apply]
        split_ifs <;> simp
      simp only [AlgEquiv.coe_toRingEquiv, AlgEquiv.trans_apply, hx,
        AlgEquiv.symm_restrictScalars, AlgEquiv.restrictScalars_apply, AlgEquiv.commutes,
        Algebra.TensorProduct.algebraMap_apply, Algebra.TensorProduct.congr_apply,
        Algebra.TensorProduct.map_tmul, map_one, Algebra.algebraMap_self, RingHom.id_apply,
        AlgEquiv.coe_toAlgHom, AlgEquiv.apply_symm_apply]
      simpa [Algebra.TensorProduct.algebraMap_apply] using φ.commutes x

variable (φ : L ⊗[K] A ≃ₐ[L] Matrix n n L)

/-- The defining formula of `splittingAut`. -/
theorem splittingAut_apply (σ : L ≃ₐ[K] L) (m : Matrix n n L) :
    splittingAut φ σ m = φ (Algebra.TensorProduct.congr σ .refl (φ.symm (m.map σ.symm))) :=
  (rfl)

/-- On an entrywise image `σ(m)`, `splittingAut φ σ` is `σ ⊗ 1` transported along `φ`. -/
@[simp]
theorem splittingAut_map (σ : L ≃ₐ[K] L) (m : Matrix n n L) :
    splittingAut φ σ (m.map σ) = φ (Algebra.TensorProduct.congr σ .refl (φ.symm m)) := by
  simp only [splittingAut_apply, Matrix.map_map, Function.comp_def, AlgEquiv.symm_apply_apply,
    Matrix.map_id']

/-- **Twisted multiplicativity**: `splittingAut φ (στ) = splittingAut φ σ ∘ σ ∘ splittingAut φ τ ∘
σ⁻¹`, the cocycle condition for `σ ↦ splittingAut φ σ` with values in the automorphisms of
`Mₙ(L)`. -/
theorem splittingAut_mul (σ τ : L ≃ₐ[K] L) (m : Matrix n n L) :
    splittingAut φ (σ * τ) (m.map σ) = splittingAut φ σ ((splittingAut φ τ m).map σ) := by
  obtain ⟨m, rfl⟩ := τ.mapMatrix.surjective m
  have hm : (τ.mapMatrix m).map σ = m.map ⇑(σ * τ) := by
    ext; simp [AlgEquiv.mul_apply]
  have ht (x : L ⊗[K] A) : Algebra.TensorProduct.congr (σ * τ) .refl x =
      Algebra.TensorProduct.congr σ .refl (Algebra.TensorProduct.congr τ .refl x) := by
    induction x using TensorProduct.inductionOn with
    | tmul x a => simp [AlgEquiv.mul_apply]
    | add x y hx hy => simp only [map_add, hx, hy]
  rw [hm, splittingAut_map, AlgEquiv.mapMatrix_apply, splittingAut_map, splittingAut_map,
    AlgEquiv.symm_apply_apply, ht]

end CommSemiring

section CommRing

variable {L : Type v} [CommRing L] [Algebra K L] (φ : L ⊗[K] A ≃ₐ[L] Matrix n n L)

/-- For a family `g` of conjugators for `φ`, `g_στ` is a unit scalar times `g_σ · σ(g_τ)`, because
both conjugate like `splittingAut φ (στ)`. -/
private theorem exists_scalar_mul_eq (g : (L ≃ₐ[K] L) → GL n L)
    (hg : ∀ σ m, (g σ : Matrix n n L) * m * ((g σ)⁻¹ : GL n L) = splittingAut φ σ m)
    (σ τ : L ≃ₐ[K] L) :
    ∃ u : Lˣ, scalar n u * (g σ * map (σ : L →+* L) (g τ)) = g (σ * τ) := by
  have hcoe (x : GL n L) : ((map (σ : L →+* L) x : GL n L) : Matrix n n L) =
      (x : Matrix n n L).map σ := by
    ext; simp
  refine exists_scalar_mul_eq_of_forall_conj_eq fun m ↦ ?_
  obtain ⟨m, rfl⟩ := σ.mapMatrix.surjective m
  rw [hg, AlgEquiv.mapMatrix_apply, splittingAut_mul, ← hg, ← hg]
  simp only [Matrix.map_mul, _root_.mul_inv_rev, Units.val_mul, ← map_inv, hcoe, mul_assoc]

variable [Nonempty n]

/-- The **`2`-cocycle of a family of conjugators** for a splitting `φ : L ⊗[K] A ≃ₐ[L] Mₙ(L)`:
given `g_σ ∈ GL_n(L)` with `splittingAut φ σ` equal to conjugation by `g_σ` for every `σ`, the
value `c(σ, τ)` is the unit scalar with `c(σ, τ) · g_σ · σ(g_τ) = g_στ`, characterized by
`TauCeti.TwoCocycle.ofConjugators_toFun_eq_iff`. -/
noncomputable def TwoCocycle.ofConjugators (g : (L ≃ₐ[K] L) → GL n L)
    (hg : ∀ σ m, (g σ : Matrix n n L) * m * ((g σ)⁻¹ : GL n L) = splittingAut φ σ m) :
    TwoCocycle K L where
  toFun σ τ := (exists_scalar_mul_eq φ g hg σ τ).choose
  isMulCocycle₂ σ τ ρ := by
    set c : (L ≃ₐ[K] L) → (L ≃ₐ[K] L) → Lˣ := fun σ τ ↦ (exists_scalar_mul_eq φ g hg σ τ).choose
    have hc σ τ : scalar n (c σ τ) * (g σ * map (σ : L →+* L) (g τ)) = g (σ * τ) :=
      (exists_scalar_mul_eq φ g hg σ τ).choose_spec
    have hmap (x : GL n L) : map (σ : L →+* L) (map (τ : L →+* L) x) =
        map ((σ * τ : L ≃ₐ[K] L) : L →+* L) x := by
      ext; simp [AlgEquiv.mul_apply]
    have hσ : σ • c τ ρ = Units.map (σ : L →+* L) (c τ ρ) :=
      Units.ext (by simp [AlgEquiv.smul_units_def])
    -- both sides times `g_σ · σ(g_τ) · στ(g_ρ)` are `g_στρ`, and scalars are injective
    apply scalar_injective (n := n)
    apply mul_right_cancel (b := g σ * map (σ : L →+* L) (g τ) *
      map ((σ * τ : L ≃ₐ[K] L) : L →+* L) (g ρ))
    calc scalar n (c (σ * τ) ρ * c σ τ) * (g σ * map (σ : L →+* L) (g τ) *
          map ((σ * τ : L ≃ₐ[K] L) : L →+* L) (g ρ))
        = scalar n (c (σ * τ) ρ) * ((scalar n (c σ τ) * (g σ * map (σ : L →+* L) (g τ))) *
          map ((σ * τ : L ≃ₐ[K] L) : L →+* L) (g ρ)) := by simp only [map_mul, mul_assoc]
      _ = g (σ * (τ * ρ)) := by rw [hc, hc, mul_assoc]
      _ = scalar n (c σ (τ * ρ)) * (g σ * map (σ : L →+* L)
          (scalar n (c τ ρ) * (g τ * map (τ : L →+* L) (g ρ)))) := by rw [hc, hc]
      _ = scalar n (σ • c τ ρ * c σ (τ * ρ)) * (g σ * map (σ : L →+* L) (g τ) *
          map ((σ * τ : L ≃ₐ[K] L) : L →+* L) (g ρ)) := by
        rw [map_mul, map_mul, hmap, map_scalar, ← hσ, mul_comm (σ • c τ ρ), map_mul,
          ← mul_assoc (g σ), ← GeneralLinearGroup.scalar_commute]
        simp only [mul_assoc]

/-- The defining property of `TwoCocycle.ofConjugators`:
`c(σ, τ) · g_σ · σ(g_τ) = g_στ`. -/
theorem TwoCocycle.scalar_ofConjugators_mul (g : (L ≃ₐ[K] L) → GL n L)
    (hg : ∀ σ m, (g σ : Matrix n n L) * m * ((g σ)⁻¹ : GL n L) = splittingAut φ σ m)
    (σ τ : L ≃ₐ[K] L) :
    scalar n ((ofConjugators φ g hg).toFun σ τ) * (g σ * map (σ : L →+* L) (g τ)) =
      g (σ * τ) :=
  (exists_scalar_mul_eq φ g hg σ τ).choose_spec

/-- **Characterization of the cocycle of a conjugator family**: `c(σ, τ)` is the unique unit `u`
with `u · g_σ · σ(g_τ) = g_στ`. -/
theorem TwoCocycle.ofConjugators_toFun_eq_iff (g : (L ≃ₐ[K] L) → GL n L)
    (hg : ∀ σ m, (g σ : Matrix n n L) * m * ((g σ)⁻¹ : GL n L) = splittingAut φ σ m)
    (σ τ : L ≃ₐ[K] L) (u : Lˣ) :
    (ofConjugators φ g hg).toFun σ τ = u ↔
      scalar n u * (g σ * map (σ : L →+* L) (g τ)) = g (σ * τ) := by
  refine ⟨fun h ↦ h ▸ scalar_ofConjugators_mul φ g hg σ τ, fun h ↦ scalar_injective (n := n) ?_⟩
  exact mul_right_cancel ((scalar_ofConjugators_mul φ g hg σ τ).trans h.symm)

end CommRing

section Field

variable {L : Type v} [Field L] [Algebra K L] (φ : L ⊗[K] A ≃ₐ[L] Matrix n n L) [Nonempty n]

/-- By Skolem–Noether, each `splittingAut φ σ` is conjugation by an invertible matrix. -/
private theorem exists_mul_mul_inv_eq_splittingAut (σ : L ≃ₐ[K] L) :
    ∃ g : GL n L, ∀ m, (g : Matrix n n L) * m * ((g⁻¹ : GL n L) : Matrix n n L) =
      splittingAut φ σ m :=
  (exists_unit_conj_of_algEquiv L (splittingAut φ σ)).imp fun _ hg m ↦ (hg m).symm

/-- A chosen conjugator `g_σ ∈ GL_n(L)` for `splittingAut φ σ`, so that `splittingAut φ σ` is
`m ↦ g_σ * m * g_σ⁻¹`. It is determined by `φ` and `σ` only up to a unit scalar. -/
noncomputable def splittingConjugator (σ : L ≃ₐ[K] L) : GL n L :=
  (exists_mul_mul_inv_eq_splittingAut φ σ).choose

/-- `splittingAut φ σ` is conjugation by `splittingConjugator φ σ`. -/
theorem splittingConjugator_mul_mul_inv (σ : L ≃ₐ[K] L) (m : Matrix n n L) :
    (splittingConjugator φ σ : Matrix n n L) * m *
      ((splittingConjugator φ σ)⁻¹ : GL n L) = splittingAut φ σ m :=
  (exists_mul_mul_inv_eq_splittingAut φ σ).choose_spec m

/-- The **cocycle of a split algebra with chosen descent data**: for a splitting
`φ : L ⊗[K] A ≃ₐ[L] Mₙ(L)` with `n` nonempty, the `2`-cocycle of the conjugators
`splittingConjugator φ σ`, that is, the unit scalars `c(σ, τ)` with
`c(σ, τ) · g_σ · σ(g_τ) = g_στ`. -/
noncomputable def cocycleOfSplitting : TwoCocycle K L :=
  TwoCocycle.ofConjugators φ (splittingConjugator φ) (splittingConjugator_mul_mul_inv φ)

/-- The defining property of `cocycleOfSplitting`: with `g_σ = splittingConjugator φ σ`,
`c(σ, τ) · g_σ · σ(g_τ) = g_στ`. -/
theorem scalar_cocycleOfSplitting_mul (σ τ : L ≃ₐ[K] L) :
    scalar n ((cocycleOfSplitting φ).toFun σ τ) *
        (splittingConjugator φ σ * map (σ : L →+* L) (splittingConjugator φ τ)) =
      splittingConjugator φ (σ * τ) :=
  TwoCocycle.scalar_ofConjugators_mul φ _ _ σ τ

/-- **Characterization of the cocycle of a split algebra**: with `g_σ = splittingConjugator φ σ`,
`c(σ, τ)` is the unique unit `u` with `u · g_σ · σ(g_τ) = g_στ`. -/
theorem cocycleOfSplitting_toFun_eq_iff (σ τ : L ≃ₐ[K] L) (u : Lˣ) :
    (cocycleOfSplitting φ).toFun σ τ = u ↔
      scalar n u * (splittingConjugator φ σ * map (σ : L →+* L) (splittingConjugator φ τ)) =
        splittingConjugator φ (σ * τ) :=
  TwoCocycle.ofConjugators_toFun_eq_iff φ _ _ σ τ u

end Field

end TauCeti
