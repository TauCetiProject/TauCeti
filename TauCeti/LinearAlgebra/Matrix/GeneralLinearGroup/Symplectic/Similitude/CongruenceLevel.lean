/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.LinearAlgebra.Matrix.GeneralLinearGroup.Symplectic.Similitude.Basic
-- `PadicInt.toZModPow` occurs in the statements of the `p`-adic specialization.
public import Mathlib.NumberTheory.Padics.RingHoms
-- `QuotientGroup.quotientKerEquivOfSurjective` gives the quotient `Γ₀ / Γ₁ ≃* GL`.
public import Mathlib.GroupTheory.QuotientGroup.Basic
-- Non-public, used only in the proofs: block products, the Levi embedding used to lift the
-- upper-left block, lifting invertible matrices along a local ring hom, and the locality of
-- truncation modulo `p ^ m`.
import TauCeti.Data.Matrix.Block
import TauCeti.LinearAlgebra.Matrix.GeneralLinearGroup.Map
import TauCeti.LinearAlgebra.Matrix.GeneralLinearGroup.Symplectic.Levi
import TauCeti.NumberTheory.Padics.RingHoms

/-!
# The congruence level subgroups `Γ₀`, `Γ₁`, `Γ` of the symplectic similitude group

Write a similitude `γ ∈ GSp(l ⊕ l, R)` in `l × l` blocks as `γ = (A B; C D)`, with multiplier
`c(γ)`. For a ring morphism `f : R →+* S`, write `f(γ)` for the reduction of `γ` along `f`
(`TauCeti.GSp.map l f γ`), applying `f` entrywise. The **congruence level subgroups** of
`GSp(l ⊕ l, R)` at `f` are

* `Γ(f) = {γ : f(γ) = 1}`, the kernel of reduction (`TauCeti.GSp.Gamma`);
* `Γ₁(f) = {γ : f(γ) = (1 ∗; 0 1)}` (`TauCeti.GSp.Gamma1`);
* `Γ₀(f) = {γ : f(C) = 0 and f(c(γ)) = 1}` (`TauCeti.GSp.Gamma0`).

For `R = ℤ_p` and `f = PadicInt.toZModPow m`, the reduction modulo `pᵐ`, these are Scholze's
level groups `Γ(pᵐ) ⊆ Γ₁(pᵐ) ⊆ Γ₀(pᵐ)` of `GSp_2g(ℤ_p)` (Scholze, Definition 3.1.1), with the
similitude condition `c(γ) ≡ 1 mod pᵐ` in `Γ₀(pᵐ)`. That condition is stronger than the printed
`det γ ≡ 1 mod pᵐ` in genus `g > 1`, since `det γ = c(γ) ^ g`
(`TauCeti.GSp.det_eq_multiplier_pow`).

The block upper-triangular similitudes form the Siegel parabolic subgroup
(`TauCeti.GSp.siegelParabolic`), and on it the upper-left block `A` is a group morphism to
`GL l S` (`TauCeti.GSp.upperLeftHom`): the lower-left block vanishes, so `(γδ)₁₁ = A_γ A_δ`.
Its composite with reduction, `TauCeti.GSp.Gamma0.upperLeftHom`, has kernel `Γ₁(f)`, because a
block upper-triangular similitude satisfies `A Dᵀ = c • 1`, so `A = 1` and `c = 1` force `D = 1`.
Hence `Γ₁(f)` is normal in `Γ₀(f)`; when `f` is surjective and reflects units, as reduction modulo
`pᵐ` does for `m ≥ 1`, every invertible `A` lifts to the Levi element `diag(Ã, (Ã⁻¹)ᵀ)`, and

```text
Γ₀(f) / Γ₁(f) ≃* GL l S        (TauCeti.GSp.Gamma0.quotientGamma1EquivGL).
```

The kernel `Γ(f)` is normal in `GSp(l ⊕ l, R)`. The multiplier carries each of the three groups
onto the kernel of `Rˣ → Sˣ` (`TauCeti.GSp.map_multiplier_Gamma0` and its companions), which for
`ℤ_p` and `m ≥ 1` is `U_m = 1 + pᵐ ℤ_p`; the Siegel cocharacter `diag(1, u)` of a unit
`u ≡ 1` already lies in `Γ(f)`. A factorization `f' = g ∘ f` gives inclusions of level groups,
which for `ℤ_p` is monotonicity in the depth `m`; at depth `m = 0` all three groups are the
whole group.

## Main definitions

* `TauCeti.GSp.siegelParabolic`: the similitudes with vanishing lower-left block.
* `TauCeti.GSp.upperLeftHom`: the upper-left block, a morphism from the Siegel parabolic to `GL`.
* `TauCeti.GSp.Gamma`, `TauCeti.GSp.Gamma1`, `TauCeti.GSp.Gamma0`: the level subgroups.
* `TauCeti.GSp.Gamma0.upperLeftHom`: the upper-left block of the reduction, on `Γ₀(f)`.
* `TauCeti.GSp.Gamma0.quotientGamma1EquivGL`: the isomorphism `Γ₀(f) / Γ₁(f) ≃* GL l S`.

## Main results

* `TauCeti.GSp.mem_Gamma_iff`, `TauCeti.GSp.mem_Gamma1_iff`, `TauCeti.GSp.mem_Gamma0_iff`: the
  congruence conditions.
* `TauCeti.GSp.Gamma_le_Gamma1`, `TauCeti.GSp.Gamma1_le_Gamma0`: `Γ(f) ⊆ Γ₁(f) ⊆ Γ₀(f)`.
* `TauCeti.GSp.Gamma.normal`, `TauCeti.GSp.Gamma0.normal_Gamma1`: the two normalities.
* `TauCeti.GSp.Gamma0.ker_upperLeftHom`: the kernel of the upper-left block on `Γ₀(f)` is `Γ₁(f)`.
* `TauCeti.GSp.map_multiplier_Gamma`, `TauCeti.GSp.map_multiplier_Gamma1`,
  `TauCeti.GSp.map_multiplier_Gamma0`: the multiplier images.
* `TauCeti.GSp.Gamma_toZModPow_le`, `TauCeti.GSp.Gamma1_toZModPow_le`,
  `TauCeti.GSp.Gamma0_toZModPow_le`: the `p`-adic level groups shrink as the depth grows.

## References

* P. Scholze, *On torsion in the cohomology of locally symmetric varieties*, Ann. of Math. 182
  (2015), §3.1, Definition 3.1.1 and the sentences after it.
-/

public section

open Matrix

namespace TauCeti

namespace GSp

universe u v

variable {l : Type*} [DecidableEq l] [Fintype l]

/-! ### Block identities -/

section Blocks

variable {R : Type u} [CommRing R]

omit [Fintype l] in
/-- The upper-left block of the identity matrix is the identity. -/
private theorem toBlocks₁₁_one : (1 : Matrix (l ⊕ l) (l ⊕ l) R).toBlocks₁₁ = 1 := by
  rw [← fromBlocks_one, toBlocks_fromBlocks₁₁]

omit [Fintype l] in
/-- The lower-left block of the identity matrix is zero. -/
private theorem toBlocks₂₁_one : (1 : Matrix (l ⊕ l) (l ⊕ l) R).toBlocks₂₁ = 0 := by
  rw [← fromBlocks_one, toBlocks_fromBlocks₂₁]

omit [Fintype l] in
/-- The lower-right block of the identity matrix is the identity. -/
private theorem toBlocks₂₂_one : (1 : Matrix (l ⊕ l) (l ⊕ l) R).toBlocks₂₂ = 1 := by
  rw [← fromBlocks_one, toBlocks_fromBlocks₂₂]

variable [Nonempty l]

/-- **The block form of the similitude condition**: for a similitude `γ = (A B; C D)` with
multiplier `c`, `A Dᵀ - B Cᵀ = c • 1`. -/
theorem toBlocks₁₁_mul_transpose_toBlocks₂₂_sub (M : GSp l R) :
    ((M : GL (l ⊕ l) R) : Matrix (l ⊕ l) (l ⊕ l) R).toBlocks₁₁ *
        ((M : GL (l ⊕ l) R) : Matrix (l ⊕ l) (l ⊕ l) R).toBlocks₂₂ᵀ -
      ((M : GL (l ⊕ l) R) : Matrix (l ⊕ l) (l ⊕ l) R).toBlocks₁₂ *
        ((M : GL (l ⊕ l) R) : Matrix (l ⊕ l) (l ⊕ l) R).toBlocks₂₁ᵀ =
      (multiplier l R M : R) • 1 := by
  have h := congrArg Matrix.toBlocks₁₂ (mul_J_mul_transpose M)
  rw [← fromBlocks_toBlocks ((M : GL (l ⊕ l) R) : Matrix (l ⊕ l) (l ⊕ l) R)] at h
  simp only [Matrix.J, fromBlocks_transpose, fromBlocks_multiply, fromBlocks_smul,
    toBlocks_fromBlocks₁₂, Matrix.mul_zero, Matrix.mul_neg, Matrix.mul_one, zero_add, add_zero,
    smul_neg, Matrix.neg_mul] at h
  rw [← neg_inj, ← h]
  abel

/-- For a block upper-triangular similitude `γ = (A B; 0 D)` with multiplier `c`,
`A Dᵀ = c • 1`. -/
theorem toBlocks₁₁_mul_transpose_toBlocks₂₂_of_toBlocks₂₁_eq_zero {M : GSp l R}
    (hM : ((M : GL (l ⊕ l) R) : Matrix (l ⊕ l) (l ⊕ l) R).toBlocks₂₁ = 0) :
    ((M : GL (l ⊕ l) R) : Matrix (l ⊕ l) (l ⊕ l) R).toBlocks₁₁ *
        ((M : GL (l ⊕ l) R) : Matrix (l ⊕ l) (l ⊕ l) R).toBlocks₂₂ᵀ =
      (multiplier l R M : R) • 1 := by
  simpa [hM] using toBlocks₁₁_mul_transpose_toBlocks₂₂_sub M

end Blocks

/-! ### The Siegel parabolic and its upper-left block -/

section SiegelParabolic

variable (l) (S : Type v) [CommRing S] [Nonempty l]

/-- The **Siegel parabolic subgroup**: the similitudes `(A B; 0 D)` with vanishing lower-left
block. -/
def siegelParabolic : Subgroup (GSp l S) where
  carrier := {M | ((M : GL (l ⊕ l) S) : Matrix (l ⊕ l) (l ⊕ l) S).toBlocks₂₁ = 0}
  mul_mem' {M N} hM hN := by
    simp only [Set.mem_ofPred_eq, Subgroup.coe_mul, Units.val_mul, toBlocks₂₁_mul] at hM hN ⊢
    rw [hM, hN, Matrix.zero_mul, Matrix.mul_zero, add_zero]
  one_mem' := by
    simp only [Set.mem_ofPred_eq, OneMemClass.coe_one, Units.val_one]
    exact toBlocks₂₁_one
  inv_mem' {M} hM := by
    simp only [Set.mem_ofPred_eq] at hM ⊢
    rw [coe_inv, ← fromBlocks_toBlocks ((M : GL (l ⊕ l) S) : Matrix (l ⊕ l) (l ⊕ l) S), hM]
    simp [Matrix.J, fromBlocks_transpose, fromBlocks_multiply, fromBlocks_smul, fromBlocks_neg]

variable {l S}

/-- Membership in the Siegel parabolic: the lower-left block vanishes. -/
theorem mem_siegelParabolic_iff {M : GSp l S} :
    M ∈ siegelParabolic l S ↔ ((M : GL (l ⊕ l) S) : Matrix (l ⊕ l) (l ⊕ l) S).toBlocks₂₁ = 0 :=
  Iff.rfl

omit [DecidableEq l] [Nonempty l] in
/-- On block upper-triangular matrices, the upper-left block of a product is the product of the
upper-left blocks. -/
private theorem toBlocks₁₁_mul_of_toBlocks₂₁_eq_zero {M N : Matrix (l ⊕ l) (l ⊕ l) S}
    (hN : N.toBlocks₂₁ = 0) : (M * N).toBlocks₁₁ = M.toBlocks₁₁ * N.toBlocks₁₁ := by
  rw [toBlocks₁₁_mul, hN, Matrix.mul_zero, add_zero]

/-- The upper-left block of an element of the Siegel parabolic is invertible, with inverse the
upper-left block of its inverse. -/
private theorem toBlocks₁₁_mul_toBlocks₁₁_inv (M : siegelParabolic l S) :
    ((M : GSp l S) : GL (l ⊕ l) S).val.toBlocks₁₁ *
        ((M⁻¹ : siegelParabolic l S) : GSp l S).val.val.toBlocks₁₁ = 1 := by
  rw [← toBlocks₁₁_mul_of_toBlocks₂₁_eq_zero (M⁻¹).property]
  simp only [InvMemClass.coe_inv, Units.mul_inv]
  exact toBlocks₁₁_one

variable (l S) in
/-- The **upper-left block** `A` of an element `(A B; 0 D)` of the Siegel parabolic, as a group
morphism to `GL l S`. -/
def upperLeftHom : siegelParabolic l S →* GL l S where
  toFun M := ⟨((M : GSp l S) : GL (l ⊕ l) S).val.toBlocks₁₁,
    ((M⁻¹ : siegelParabolic l S) : GSp l S).val.val.toBlocks₁₁,
    toBlocks₁₁_mul_toBlocks₁₁_inv M, by
      simpa only [inv_inv] using toBlocks₁₁_mul_toBlocks₁₁_inv M⁻¹⟩
  map_one' := Units.ext <| by
    simp only [OneMemClass.coe_one, Units.val_one]
    exact toBlocks₁₁_one
  map_mul' M N := Units.ext <| by
    simp only [Subgroup.coe_mul, Units.val_mul]
    exact toBlocks₁₁_mul_of_toBlocks₂₁_eq_zero N.property

/-- The upper-left block morphism takes an element to its upper-left block. -/
@[simp]
theorem coe_upperLeftHom (M : siegelParabolic l S) :
    (upperLeftHom l S M : Matrix l l S) = ((M : GSp l S) : GL (l ⊕ l) S).val.toBlocks₁₁ :=
  (rfl)

end SiegelParabolic

/-! ### The level subgroups -/

variable (l) {R : Type u} [CommRing R] {S : Type v} [CommRing S]

/-- The **principal congruence subgroup** `Γ(f)`: the kernel of reduction along `f`. For
`f = PadicInt.toZModPow m` this is `Γ(pᵐ) = {γ : γ ≡ 1 mod pᵐ}`. -/
def Gamma (f : R →+* S) : Subgroup (GSp l R) :=
  (map l f).ker

variable {l}

/-- Membership in `Γ(f)`: the reduction is the identity matrix. -/
theorem mem_Gamma_iff {f : R →+* S} {M : GSp l R} :
    M ∈ Gamma l f ↔ ((M : GL (l ⊕ l) R) : Matrix (l ⊕ l) (l ⊕ l) R).map f = 1 := by
  rw [Gamma, MonoidHom.mem_ker, ← Subtype.coe_inj, coe_map, OneMemClass.coe_one, Units.ext_iff,
    Matrix.GeneralLinearGroup.val_map_apply, Units.val_one]

/-- `Γ(f)` is normal, as a kernel. -/
instance Gamma.normal (f : R →+* S) : (Gamma l f).Normal :=
  MonoidHom.normal_ker _

/-- Over a zero target ring, such as `ZMod (p ^ 0)`, `Γ(f)` is the whole group. -/
theorem Gamma_eq_top_of_subsingleton [Subsingleton S] (f : R →+* S) : Gamma l f = ⊤ :=
  eq_top_iff.2 fun _ _ ↦ Subsingleton.elim _ _

/-- A factorization `f' = g ∘ f` gives `Γ(f) ⊆ Γ(f')`. -/
theorem Gamma_le_of_comp {T : Type*} [CommRing T] {f : R →+* S} {f' : R →+* T} (g : S →+* T)
    (h : g.comp f = f') : Gamma l f ≤ Gamma l f' := by
  intro M hM
  rw [Gamma, MonoidHom.mem_ker] at hM ⊢
  rw [← h, map_comp, MonoidHom.comp_apply, hM, map_one]

section Level

variable [Nonempty l]

variable (l) in
/-- The **congruence subgroup** `Γ₀(f)`: the similitudes whose reduction along `f` is block
upper-triangular with multiplier `1`. For `f = PadicInt.toZModPow m` this is Scholze's
`Γ₀(pᵐ) = {γ : γ ≡ (∗ ∗; 0 ∗) mod pᵐ and c(γ) ≡ 1 mod pᵐ}`. -/
noncomputable def Gamma0 (f : R →+* S) : Subgroup (GSp l R) :=
  (siegelParabolic l S).comap (map l f) ⊓ ((Units.map (f : R →* S)).comp (multiplier l R)).ker

/-- Membership in `Γ₀(f)`: the reduction has vanishing lower-left block and the multiplier
reduces to `1`. -/
theorem mem_Gamma0_iff {f : R →+* S} {M : GSp l R} :
    M ∈ Gamma0 l f ↔
      (((M : GL (l ⊕ l) R) : Matrix (l ⊕ l) (l ⊕ l) R).map f).toBlocks₂₁ = 0 ∧
        f (multiplier l R M : R) = 1 := by
  rw [Gamma0, Subgroup.mem_inf, Subgroup.mem_comap, mem_siegelParabolic_iff, MonoidHom.mem_ker,
    coe_map, MonoidHom.comp_apply, Units.ext_iff]
  rfl

/-- The reduction of an element of `Γ₀(f)` lies in the Siegel parabolic over `S`. -/
private theorem map_mem_siegelParabolic {f : R →+* S} {M : GSp l R} (hM : M ∈ Gamma0 l f) :
    map l f M ∈ siegelParabolic l S :=
  (Subgroup.mem_inf.1 hM).left

namespace Gamma0

variable (l) in
/-- The **upper-left block of the reduction** on `Γ₀(f)`: `γ ↦ f(A)`, a group morphism to `GL l S`.
Its kernel is `Γ₁(f)` (`TauCeti.GSp.Gamma0.ker_upperLeftHom`). -/
noncomputable def upperLeftHom (f : R →+* S) : Gamma0 l f →* GL l S :=
  (GSp.upperLeftHom l S).comp
    (((map l f).comp (Gamma0 l f).subtype).codRestrict (siegelParabolic l S)
      fun M ↦ map_mem_siegelParabolic M.property)

/-- The upper-left block of the reduction of `γ ∈ Γ₀(f)`. -/
@[simp]
theorem coe_upperLeftHom (f : R →+* S) (M : Gamma0 l f) :
    (upperLeftHom l f M : Matrix l l S) =
      (((M : GSp l R) : GL (l ⊕ l) R).val.map f).toBlocks₁₁ := by
  simp [upperLeftHom]

end Gamma0

variable (l) in
/-- The **congruence subgroup** `Γ₁(f)`: the similitudes whose reduction along `f` has the form
`(1 ∗; 0 1)` (`TauCeti.GSp.mem_Gamma1_iff`), defined as the kernel of the upper-left block of
the reduction on `Γ₀(f)`. For `f = PadicInt.toZModPow m` this is
`Γ₁(pᵐ) = {γ : γ ≡ (1 ∗; 0 1) mod pᵐ}`. -/
noncomputable def Gamma1 (f : R →+* S) : Subgroup (GSp l R) :=
  (Gamma0.upperLeftHom l f).ker.map (Gamma0 l f).subtype

/-- `Γ₁(f) ⊆ Γ₀(f)`. -/
theorem Gamma1_le_Gamma0 (f : R →+* S) : Gamma1 l f ≤ Gamma0 l f := by
  rintro _ ⟨M, -, rfl⟩
  exact M.property

/-- **Membership in `Γ₁(f)`**: the reduction is `(1 ∗; 0 1)`. -/
theorem mem_Gamma1_iff {f : R →+* S} {M : GSp l R} :
    M ∈ Gamma1 l f ↔
      (((M : GL (l ⊕ l) R) : Matrix (l ⊕ l) (l ⊕ l) R).map f).toBlocks₁₁ = 1 ∧
        (((M : GL (l ⊕ l) R) : Matrix (l ⊕ l) (l ⊕ l) R).map f).toBlocks₂₁ = 0 ∧
          (((M : GL (l ⊕ l) R) : Matrix (l ⊕ l) (l ⊕ l) R).map f).toBlocks₂₂ = 1 := by
  have hAD (N : GSp l R)
      (h : (((N : GL (l ⊕ l) R) : Matrix (l ⊕ l) (l ⊕ l) R).map f).toBlocks₂₁ = 0) :
      (((N : GL (l ⊕ l) R) : Matrix (l ⊕ l) (l ⊕ l) R).map f).toBlocks₁₁ *
          (((N : GL (l ⊕ l) R) : Matrix (l ⊕ l) (l ⊕ l) R).map f).toBlocks₂₂ᵀ =
        f (multiplier l R N : R) • 1 := by
    have := toBlocks₁₁_mul_transpose_toBlocks₂₂_of_toBlocks₂₁_eq_zero (M := map l f N)
    simp only [coe_map, Matrix.GeneralLinearGroup.val_map_apply, multiplier_map,
      Units.coe_map, MonoidHom.coe_ofClass] at this
    exact this h
  constructor
  · rintro ⟨M, hM, rfl⟩
    rw [SetLike.mem_coe, MonoidHom.mem_ker, Units.ext_iff, Gamma0.coe_upperLeftHom,
      Units.val_one] at hM
    obtain ⟨h₂₁, hc⟩ := mem_Gamma0_iff.1 M.property
    refine ⟨hM, h₂₁, ?_⟩
    have := hAD M h₂₁
    rw [hM, Matrix.one_mul, hc, one_smul] at this
    simpa using congrArg Matrix.transpose this
  · rintro ⟨h₁₁, h₂₁, h₂₂⟩
    have hc : f (multiplier l R M : R) = 1 := by
      have := hAD M h₂₁
      rw [h₁₁, h₂₂, transpose_one, Matrix.one_mul] at this
      have h := congrFun (congrFun this (Classical.arbitrary l)) (Classical.arbitrary l)
      simpa using h.symm
    have hM : M ∈ Gamma0 l f := mem_Gamma0_iff.2 ⟨h₂₁, hc⟩
    exact ⟨⟨M, hM⟩, by
      rw [SetLike.mem_coe, MonoidHom.mem_ker, Units.ext_iff, Gamma0.coe_upperLeftHom,
        Units.val_one]
      exact h₁₁, rfl⟩

/-- `Γ(f) ⊆ Γ₁(f)`. -/
theorem Gamma_le_Gamma1 (f : R →+* S) : Gamma l f ≤ Gamma1 l f := by
  intro M hM
  rw [mem_Gamma_iff] at hM
  rw [mem_Gamma1_iff, hM]
  exact ⟨toBlocks₁₁_one, toBlocks₂₁_one, toBlocks₂₂_one⟩

namespace Gamma0

/-- **The kernel of the upper-left block of the reduction on `Γ₀(f)` is `Γ₁(f)`.** -/
theorem ker_upperLeftHom (f : R →+* S) :
    (upperLeftHom l f).ker = (Gamma1 l f).subgroupOf (Gamma0 l f) := by
  exact (Subgroup.comap_map_eq_self_of_injective (Gamma0 l f).subtype_injective _).symm

/-- **`Γ₁(f)` is normal in `Γ₀(f)`.** -/
instance normal_Gamma1 (f : R →+* S) : ((Gamma1 l f).subgroupOf (Gamma0 l f)).Normal := by
  rw [← ker_upperLeftHom]
  exact MonoidHom.normal_ker _

/-- When `f` is surjective and reflects units, the upper-left block of the reduction is
surjective on `Γ₀(f)`: every element of `GL l S` is the upper-left block of the reduction of
some `γ ∈ Γ₀(f)`. -/
theorem upperLeftHom_surjective {f : R →+* S} [IsLocalHom f] (hf : Function.Surjective f) :
    Function.Surjective (upperLeftHom l f) := by
  intro A
  obtain ⟨B, rfl⟩ := Matrix.GeneralLinearGroup.map_surjective hf A
  set L : GSp l R :=
    ⟨GLSymplectic.leviHom B, GLSymplectic_le_GSp l R (GLSymplectic.leviHom B).property⟩
  have hL : ((L : GL (l ⊕ l) R) : Matrix (l ⊕ l) (l ⊕ l) R) =
      fromBlocks (B : Matrix l l R) 0 0 ((B⁻¹ : GL l R) : Matrix l l R)ᵀ :=
    GLSymplectic.coe_leviHom B
  have hc : multiplier l R L = 1 := (mem_GLSymplectic_iff L).1 (GLSymplectic.leviHom B).property
  have hL0 : L ∈ Gamma0 l f := by
    rw [mem_Gamma0_iff, hL, hc, Units.val_one, map_one, fromBlocks_map]
    simp
  refine ⟨⟨L, hL0⟩, Units.ext ?_⟩
  rw [coe_upperLeftHom, hL, fromBlocks_map, toBlocks_fromBlocks₁₁]
  rfl

variable (l) in
/-- **`Γ₀(f) / Γ₁(f) ≃* GL l S`** through the upper-left block of the reduction, when `f` is
surjective and reflects units. For reduction modulo `pᵐ` with `m ≥ 1` this is
`Γ₀(pᵐ) / Γ₁(pᵐ) ≃* GL_g(ℤ/pᵐ)`. -/
noncomputable def quotientGamma1EquivGL {f : R →+* S} [IsLocalHom f]
    (hf : Function.Surjective f) : Gamma0 l f ⧸ (Gamma1 l f).subgroupOf (Gamma0 l f) ≃* GL l S :=
  (QuotientGroup.quotientMulEquivOfEq (ker_upperLeftHom f).symm).trans
    (QuotientGroup.quotientKerEquivOfSurjective _ (upperLeftHom_surjective hf))

/-- The isomorphism `Γ₀(f) / Γ₁(f) ≃* GL l S` sends the class of `γ` to the upper-left block of
its reduction. -/
@[simp]
theorem quotientGamma1EquivGL_mk {f : R →+* S} [IsLocalHom f] (hf : Function.Surjective f)
    (M : Gamma0 l f) :
    quotientGamma1EquivGL l hf (QuotientGroup.mk M) = upperLeftHom l f M :=
  (rfl)

end Gamma0

/-- `Γ(f) ⊆ Γ₀(f)`. -/
theorem Gamma_le_Gamma0 (f : R →+* S) : Gamma l f ≤ Gamma0 l f :=
  (Gamma_le_Gamma1 f).trans (Gamma1_le_Gamma0 f)

/-- Over a zero target ring, `Γ₁(f)` is the whole group. -/
theorem Gamma1_eq_top_of_subsingleton [Subsingleton S] (f : R →+* S) : Gamma1 l f = ⊤ :=
  eq_top_iff.2 <| (Gamma_eq_top_of_subsingleton f).ge.trans (Gamma_le_Gamma1 f)

/-- Over a zero target ring, `Γ₀(f)` is the whole group. -/
theorem Gamma0_eq_top_of_subsingleton [Subsingleton S] (f : R →+* S) : Gamma0 l f = ⊤ :=
  eq_top_iff.2 <| (Gamma_eq_top_of_subsingleton f).ge.trans (Gamma_le_Gamma0 f)

/-- A factorization `f' = g ∘ f` gives `Γ₀(f) ⊆ Γ₀(f')`. -/
theorem Gamma0_le_of_comp {T : Type*} [CommRing T] {f : R →+* S} {f' : R →+* T} (g : S →+* T)
    (h : g.comp f = f') : Gamma0 l f ≤ Gamma0 l f' := by
  intro M hM
  rw [mem_Gamma0_iff] at hM ⊢
  obtain ⟨h₂₁, hc⟩ := hM
  subst h
  refine ⟨?_, by rw [RingHom.comp_apply, hc, map_one]⟩
  have hmap : ((M : GL (l ⊕ l) R) : Matrix (l ⊕ l) (l ⊕ l) R).map (g.comp f) =
      (((M : GL (l ⊕ l) R) : Matrix (l ⊕ l) (l ⊕ l) R).map f).map g := by
    rw [Matrix.map_map]
    rfl
  -- Entrywise maps commute with taking blocks.
  have h₂₁map (N : Matrix (l ⊕ l) (l ⊕ l) S) : (N.map g).toBlocks₂₁ = N.toBlocks₂₁.map g := rfl
  rw [hmap, h₂₁map, h₂₁, Matrix.map_zero _ (map_zero g)]

/-- A factorization `f' = g ∘ f` gives `Γ₁(f) ⊆ Γ₁(f')`. -/
theorem Gamma1_le_of_comp {T : Type*} [CommRing T] {f : R →+* S} {f' : R →+* T} (g : S →+* T)
    (h : g.comp f = f') : Gamma1 l f ≤ Gamma1 l f' := by
  intro M hM
  rw [mem_Gamma1_iff] at hM ⊢
  obtain ⟨h₁₁, h₂₁, h₂₂⟩ := hM
  subst h
  have hmap : ((M : GL (l ⊕ l) R) : Matrix (l ⊕ l) (l ⊕ l) R).map (g.comp f) =
      (((M : GL (l ⊕ l) R) : Matrix (l ⊕ l) (l ⊕ l) R).map f).map g := by
    rw [Matrix.map_map]
    rfl
  -- Entrywise maps commute with taking blocks.
  have h₁₁map (N : Matrix (l ⊕ l) (l ⊕ l) S) : (N.map g).toBlocks₁₁ = N.toBlocks₁₁.map g := rfl
  have h₂₁map (N : Matrix (l ⊕ l) (l ⊕ l) S) : (N.map g).toBlocks₂₁ = N.toBlocks₂₁.map g := rfl
  have h₂₂map (N : Matrix (l ⊕ l) (l ⊕ l) S) : (N.map g).toBlocks₂₂ = N.toBlocks₂₂.map g := rfl
  rw [hmap, h₁₁map, h₂₁map, h₂₂map, h₁₁, h₂₁, h₂₂, Matrix.map_one _ (map_zero g) (map_one g),
    Matrix.map_zero _ (map_zero g)]
  exact ⟨rfl, rfl, rfl⟩

/-! ### Multiplier images -/

omit [Nonempty l] in
/-- The Siegel cocharacter of a unit reducing to `1` lies in `Γ(f)`. -/
theorem siegelCocharacter_mem_Gamma {f : R →+* S} {u : Rˣ}
    (hu : u ∈ (Units.map (f : R →* S)).ker) : siegelCocharacter l R u ∈ Gamma l f := by
  rw [Gamma, MonoidHom.mem_ker, map_siegelCocharacter, MonoidHom.mem_ker.1 hu, map_one]

/-- The multiplier carries `Γ₀(f)` into the kernel of `Rˣ → Sˣ`. -/
private theorem map_multiplier_Gamma0_le (f : R →+* S) :
    (Gamma0 l f).map (multiplier l R) ≤ (Units.map (f : R →* S)).ker := by
  rintro _ ⟨M, hM, rfl⟩
  rw [MonoidHom.mem_ker, Units.ext_iff]
  exact (mem_Gamma0_iff.1 hM).right

/-- The kernel of `Rˣ → Sˣ` is contained in the multiplier image of `Γ(f)`. -/
private theorem ker_le_map_multiplier_Gamma (f : R →+* S) :
    (Units.map (f : R →* S)).ker ≤ (Gamma l f).map (multiplier l R) :=
  fun u hu ↦ ⟨_, siegelCocharacter_mem_Gamma hu, multiplier_siegelCocharacter u⟩

/-- **The multiplier image of `Γ₀(f)`** is the kernel of `Rˣ → Sˣ`; for reduction modulo `pᵐ`
with `m ≥ 1` this is `U_m = 1 + pᵐ ℤ_p`. -/
theorem map_multiplier_Gamma0 (f : R →+* S) :
    (Gamma0 l f).map (multiplier l R) = (Units.map (f : R →* S)).ker :=
  le_antisymm (map_multiplier_Gamma0_le f)
    ((ker_le_map_multiplier_Gamma f).trans (Subgroup.map_mono (Gamma_le_Gamma0 f)))

/-- The multiplier image of `Γ₁(f)` is the kernel of `Rˣ → Sˣ`. -/
theorem map_multiplier_Gamma1 (f : R →+* S) :
    (Gamma1 l f).map (multiplier l R) = (Units.map (f : R →* S)).ker :=
  le_antisymm ((Subgroup.map_mono (Gamma1_le_Gamma0 f)).trans (map_multiplier_Gamma0_le f))
    ((ker_le_map_multiplier_Gamma f).trans (Subgroup.map_mono (Gamma_le_Gamma1 f)))

/-- The multiplier image of `Γ(f)` is the kernel of `Rˣ → Sˣ`. -/
theorem map_multiplier_Gamma (f : R →+* S) :
    (Gamma l f).map (multiplier l R) = (Units.map (f : R →* S)).ker :=
  le_antisymm ((Subgroup.map_mono (Gamma_le_Gamma0 f)).trans (map_multiplier_Gamma0_le f))
    (ker_le_map_multiplier_Gamma f)

end Level

/-! ### The `p`-adic level groups -/

section Padic

variable {p : ℕ} [Fact p.Prime]

/-- `Γ(pⁿ) ⊆ Γ(pᵐ)` for `m ≤ n`. -/
theorem Gamma_toZModPow_le {m n : ℕ} (h : m ≤ n) :
    Gamma l (PadicInt.toZModPow (p := p) n) ≤ Gamma l (PadicInt.toZModPow (p := p) m) :=
  Gamma_le_of_comp _ (PadicInt.zmod_cast_comp_toZModPow m n h)

/-- At depth zero, `Γ(p⁰)` is the whole group. -/
theorem Gamma_toZModPow_zero : Gamma l (PadicInt.toZModPow (p := p) 0) = ⊤ :=
  haveI : Subsingleton (ZMod (p ^ 0)) := ZMod.subsingleton_iff.2 (pow_zero p)
  Gamma_eq_top_of_subsingleton _

variable [Nonempty l]

/-- `Γ₁(pⁿ) ⊆ Γ₁(pᵐ)` for `m ≤ n`. -/
theorem Gamma1_toZModPow_le {m n : ℕ} (h : m ≤ n) :
    Gamma1 l (PadicInt.toZModPow (p := p) n) ≤ Gamma1 l (PadicInt.toZModPow (p := p) m) :=
  Gamma1_le_of_comp _ (PadicInt.zmod_cast_comp_toZModPow m n h)

/-- `Γ₀(pⁿ) ⊆ Γ₀(pᵐ)` for `m ≤ n`. -/
theorem Gamma0_toZModPow_le {m n : ℕ} (h : m ≤ n) :
    Gamma0 l (PadicInt.toZModPow (p := p) n) ≤ Gamma0 l (PadicInt.toZModPow (p := p) m) :=
  Gamma0_le_of_comp _ (PadicInt.zmod_cast_comp_toZModPow m n h)

/-- At depth zero, `Γ₁(p⁰)` is the whole group. -/
theorem Gamma1_toZModPow_zero : Gamma1 l (PadicInt.toZModPow (p := p) 0) = ⊤ :=
  haveI : Subsingleton (ZMod (p ^ 0)) := ZMod.subsingleton_iff.2 (pow_zero p)
  Gamma1_eq_top_of_subsingleton _

/-- At depth zero, `Γ₀(p⁰)` is the whole group. -/
theorem Gamma0_toZModPow_zero : Gamma0 l (PadicInt.toZModPow (p := p) 0) = ⊤ :=
  haveI : Subsingleton (ZMod (p ^ 0)) := ZMod.subsingleton_iff.2 (pow_zero p)
  Gamma0_eq_top_of_subsingleton _

variable (l p) in
/-- **`Γ₀(pᵐ) / Γ₁(pᵐ) ≃* GL_g(ℤ/pᵐ)`** for `m ≥ 1`, through the upper-left block modulo
`pᵐ`. -/
noncomputable def Gamma0.quotientGamma1EquivGLZModPow (m : ℕ) [NeZero m] :
    Gamma0 l (PadicInt.toZModPow (p := p) m) ⧸
        (Gamma1 l (PadicInt.toZModPow (p := p) m)).subgroupOf
          (Gamma0 l (PadicInt.toZModPow (p := p) m)) ≃*
      GL l (ZMod (p ^ m)) :=
  Gamma0.quotientGamma1EquivGL l (ZMod.ringHom_surjective _)

end Padic

end GSp

end TauCeti
