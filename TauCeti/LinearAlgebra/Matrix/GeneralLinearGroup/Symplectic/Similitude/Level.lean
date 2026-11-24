/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.LinearAlgebra.Matrix.GeneralLinearGroup.Symplectic.Similitude.Basic
public import TauCeti.LinearAlgebra.Matrix.GeneralLinearGroup.Symplectic.Levi
public import TauCeti.LinearAlgebra.Matrix.GeneralLinearGroup.Lift

import TauCeti.Data.Matrix.Block

/-!
# The level subgroups `Γ`, `Γ₁`, `Γ₀` of the symplectic similitude group

Write an element of the symplectic similitude group `GSp(l ⊕ l, R)` in `l × l` blocks as
`γ = (A B; C D)`, with multiplier `c(γ)`. For a ring homomorphism `f : R →+* S`, thought of as a
reduction map such as `ℤ_p → ℤ/pᵐ`, this file defines the three level subgroups

* `Γ(f) = {γ : f(γ) = 1}`, the kernel of `GSp(l ⊕ l, R) → GSp(l ⊕ l, S)`;
* `Γ₁(f) = {γ : f(γ) = (1 ∗; 0 1)}`;
* `Γ₀(f) = {γ : f(C) = 0 and f(c(γ)) = 1}`,

so that `Γ(f) ≤ Γ₁(f) ≤ Γ₀(f)`. Over `R = ℤ_p` and `f` the reduction modulo `pᵐ` these are
Scholze's level groups `Γ(pᵐ)`, `Γ₁(pᵐ)` and `Γ₀(pᵐ)` of `GSp_2g(ℤ_p)`. The similitude condition
in `Γ₀` is `f(c(γ)) = 1`, not `f(det γ) = 1`: since `det γ = c(γ)ᵍ`, the determinant condition is
weaker in genus `g > 1`.

The groups `Γ₁(f)` and `Γ₀(f)` are the preimages of two subgroups of `GSp(l ⊕ l, S)`: the
**Siegel parabolic subgroup with multiplier one** `{(A B; 0 D) : c = 1}`
(`TauCeti.GLSymplecticSimilitude.siegelParabolicOne`) and its **unipotent radical**
`{(1 B; 0 1)}` (`TauCeti.GLSymplecticSimilitude.siegelUnipotent`). The block identities
`γ⁻¹ = c(γ)⁻¹ (Dᵀ -Bᵀ; -Cᵀ Aᵀ)` and `D Aᵀ - C Bᵀ = c(γ)` show that these are subgroups, and that on
the first one `A` is invertible with inverse `Dᵀ`. This gives a homomorphism
`(A B; 0 D) ↦ A` to `GL(l, S)` with kernel the unipotent radical, split by the Levi embedding
`A ↦ diag(A, (A⁻¹)ᵀ)`. Pulled back along `f`, it is a homomorphism `Γ₀(f) →* GL(l, S)`
(`TauCeti.GLSymplecticSimilitude.Gamma0.upperLeft`) with kernel `Γ₁(f)`. Hence `Γ₁(f)` is normal
in `Γ₀(f)`, and when `f` is surjective and reflects units (as reduction `ℤ_p → ℤ/pᵐ` does)
`Γ₀(f)/Γ₁(f) ≃* GL(l, S)`.

## Main definitions

* `TauCeti.GLSymplecticSimilitude.siegelParabolicOne S` and `siegelUnipotent S`: the Siegel
  parabolic subgroup with multiplier one and its unipotent radical.
* `TauCeti.GLSymplecticSimilitude.upperLeft S`: the upper-left block on `siegelParabolicOne S`.
* `TauCeti.GLSymplecticSimilitude.Gamma f`, `Gamma1 f`, `Gamma0 f`: the level subgroups.
* `TauCeti.GLSymplecticSimilitude.Gamma0.upperLeft f`: the reduced upper-left block on `Γ₀(f)`.

## Main results

* `TauCeti.GLSymplecticSimilitude.ker_upperLeft` and `upperLeft_surjective`: the upper-left
  block is a surjection from the Siegel parabolic subgroup with multiplier one onto `GL(l, S)`
  with kernel the unipotent radical.
* `TauCeti.GLSymplecticSimilitude.mem_Gamma_iff`, `mem_Gamma1_iff` and `mem_Gamma0_iff`: the
  defining congruences.
* `TauCeti.GLSymplecticSimilitude.Gamma_le_Gamma1` and `Gamma1_le_Gamma0`: the inclusions.
* `TauCeti.GLSymplecticSimilitude.Gamma_le_Gamma_comp` (and its `Gamma1`, `Gamma0` analogues):
  the level groups grow when the reduction is followed by another ring homomorphism, which gives
  monotonicity in the depth.
* `TauCeti.GLSymplecticSimilitude.Gamma_eq_top` (and its analogues): over a zero target ring
  every level group is everything.
* `TauCeti.GLSymplecticSimilitude.Gamma0.ker_upperLeft`: the kernel of `upperLeft` is `Γ₁(f)`,
  so `Γ₁(f)` is normal in `Γ₀(f)`.
* `TauCeti.GLSymplecticSimilitude.Gamma0.quotientEquiv`: `Γ₀(f)/Γ₁(f) ≃* GL(l, S)` when `f` is
  surjective and reflects units.

## References

* P. Scholze, *On torsion in the cohomology of locally symmetric varieties*, Ann. of Math. (2)
  182 (2015), §3.1, Definition 3.1.1, where the level groups are introduced with the determinant
  condition in place of the similitude condition in `Γ₀`.
-/

public section

open Matrix

namespace TauCeti

namespace GLSymplecticSimilitude

variable {l : Type*} [DecidableEq l] [Fintype l] {R S : Type*} [CommRing R] [CommRing S]

/-! ### The Siegel parabolic subgroups over the target ring -/

section Siegel

variable (l S)

/-- The **unipotent radical of the Siegel parabolic subgroup**: the similitudes `(1 B; 0 1)`. -/
def siegelUnipotent : Subgroup (GLSymplecticSimilitude l S) where
  carrier := {M | (M : GL (l ⊕ l) S).val.toBlocks₁₁ = 1 ∧ (M : GL (l ⊕ l) S).val.toBlocks₂₁ = 0 ∧
    (M : GL (l ⊕ l) S).val.toBlocks₂₂ = 1}
  mul_mem' {M N} hM hN := by
    simp only [Set.mem_ofPred_eq, Subgroup.coe_mul, Units.val_mul, toBlocks₁₁_mul, toBlocks₂₁_mul,
      toBlocks₂₂_mul, hM.1, hM.2.1, hM.2.2, hN.1, hN.2.1, hN.2.2]
    simp
  one_mem' := by
    refine ⟨?_, ?_, ?_⟩ <;> ext i j <;> simp [toBlocks₁₁, toBlocks₂₁, toBlocks₂₂, Matrix.one_apply]
  inv_mem' {M} hM := by
    -- The inverse of `(1 B; 0 1)` is `(1 -B; 0 1)`.
    set B := (M : GL (l ⊕ l) S).val.toBlocks₁₂
    have hM' : (M : GL (l ⊕ l) S).val = fromBlocks 1 B 0 1 := by
      conv_lhs => rw [← fromBlocks_toBlocks (M : GL (l ⊕ l) S).val]
      rw [hM.1, hM.2.1, hM.2.2]
    have hinv :
        ((M⁻¹ : GLSymplecticSimilitude l S) : GL (l ⊕ l) S).val = fromBlocks 1 (-B) 0 1 := by
      rw [Subgroup.coe_inv, ← mul_one (((M : GL (l ⊕ l) S)⁻¹ : GL (l ⊕ l) S).val),
        ← show (M : GL (l ⊕ l) S).val * fromBlocks 1 (-B) 0 1 = 1 by
          rw [hM', fromBlocks_multiply]; simp,
        ← Matrix.mul_assoc, ← Units.val_mul, inv_mul_cancel, Units.val_one, Matrix.one_mul]
    refine ⟨?_, ?_, ?_⟩ <;> rw [hinv] <;> simp

/-- Over the zero ring the unipotent radical is everything. -/
theorem siegelUnipotent_eq_top [Subsingleton S] : siegelUnipotent l S = ⊤ :=
  eq_top_iff.2 fun _ _ => ⟨Subsingleton.elim _ _, Subsingleton.elim _ _, Subsingleton.elim _ _⟩

variable {l S}

/-- Membership in the unipotent radical of the Siegel parabolic subgroup. -/
theorem mem_siegelUnipotent_iff {M : GLSymplecticSimilitude l S} :
    M ∈ siegelUnipotent l S ↔ (M : GL (l ⊕ l) S).val.toBlocks₁₁ = 1 ∧
      (M : GL (l ⊕ l) S).val.toBlocks₂₁ = 0 ∧ (M : GL (l ⊕ l) S).val.toBlocks₂₂ = 1 :=
  Iff.rfl

/-- A ring homomorphism carries the unipotent radical into itself. -/
theorem siegelUnipotent_le_comap_map {T : Type*} [CommRing T] (g : S →+* T) :
    siegelUnipotent l S ≤ (siegelUnipotent l T).comap (map l g) := by
  intro M hM
  rw [Subgroup.mem_comap, mem_siegelUnipotent_iff, coe_map, GeneralLinearGroup.val_map_apply,
    toBlocks₁₁_map, toBlocks₂₁_map, toBlocks₂₂_map, hM.1, hM.2.1, hM.2.2]
  simp

variable (l S) [Nonempty l]

/-- The **Siegel parabolic subgroup with multiplier one**: the similitudes `(A B; 0 D)` with
`c = 1`, block upper-triangular for the splitting `l ⊕ l`. -/
def siegelParabolicOne : Subgroup (GLSymplecticSimilitude l S) where
  carrier := {M | (M : GL (l ⊕ l) S).val.toBlocks₂₁ = 0 ∧ multiplier l S M = 1}
  mul_mem' {M N} hM hN := by
    refine ⟨?_, by rw [map_mul, hM.2, hN.2, mul_one]⟩
    rw [Subgroup.coe_mul, Units.val_mul, toBlocks₂₁_mul, hM.1, hN.1]
    simp
  one_mem' := ⟨by ext i j; simp [toBlocks₂₁], map_one _⟩
  inv_mem' {M} hM := by
    refine ⟨?_, by rw [map_inv, hM.2, inv_one]⟩
    rw [coe_inv_eq_smul_fromBlocks, fromBlocks_smul, toBlocks_fromBlocks₂₁, hM.1]
    simp

variable {l S} in
/-- A similitude of the shape `(1 B; 0 1)` has multiplier one, by
`toBlocks₂₂_mul_transpose_sub`. -/
private theorem multiplier_eq_one_of_toBlocks {M : GLSymplecticSimilitude l S}
    (h₁₁ : (M : GL (l ⊕ l) S).val.toBlocks₁₁ = 1) (h₂₁ : (M : GL (l ⊕ l) S).val.toBlocks₂₁ = 0)
    (h₂₂ : (M : GL (l ⊕ l) S).val.toBlocks₂₂ = 1) : multiplier l S M = 1 := by
  have h := toBlocks₂₂_mul_transpose_sub M
  rw [h₁₁, h₂₁, h₂₂] at h
  simp only [transpose_one, Matrix.mul_one, Matrix.zero_mul, sub_zero] at h
  have := congrFun (congrFun h (Classical.arbitrary l)) (Classical.arbitrary l)
  exact Units.ext (by simpa using this.symm)

variable {l S}

/-- Membership in the Siegel parabolic subgroup with multiplier one. -/
theorem mem_siegelParabolicOne_iff {M : GLSymplecticSimilitude l S} :
    M ∈ siegelParabolicOne l S ↔
      (M : GL (l ⊕ l) S).val.toBlocks₂₁ = 0 ∧ multiplier l S M = 1 :=
  Iff.rfl

variable (l S) in
/-- The unipotent radical lies in the Siegel parabolic subgroup with multiplier one. -/
theorem siegelUnipotent_le_siegelParabolicOne : siegelUnipotent l S ≤ siegelParabolicOne l S :=
  fun _ hM => ⟨hM.2.1, multiplier_eq_one_of_toBlocks hM.1 hM.2.1 hM.2.2⟩

variable (l S) in
/-- Over the zero ring the Siegel parabolic subgroup with multiplier one is everything. -/
theorem siegelParabolicOne_eq_top [Subsingleton S] : siegelParabolicOne l S = ⊤ :=
  eq_top_iff.2 fun _ _ => ⟨Subsingleton.elim _ _, Subsingleton.elim _ _⟩

variable {T : Type*} [CommRing T]

/-- A ring homomorphism carries the Siegel parabolic subgroup with multiplier one into itself. -/
theorem siegelParabolicOne_le_comap_map (g : S →+* T) :
    siegelParabolicOne l S ≤ (siegelParabolicOne l T).comap (map l g) := by
  intro M hM
  refine ⟨?_, by rw [multiplier_map, hM.2, map_one]⟩
  rw [coe_map, GeneralLinearGroup.val_map_apply, toBlocks₂₁_map, hM.1]
  simp

/-- On the Siegel parabolic subgroup with multiplier one, `D Aᵀ = 1`. -/
private theorem toBlocks₂₂_mul_transpose_toBlocks₁₁ {M : GLSymplecticSimilitude l S}
    (hM : M ∈ siegelParabolicOne l S) :
    (M : GL (l ⊕ l) S).val.toBlocks₂₂ * (M : GL (l ⊕ l) S).val.toBlocks₁₁ᵀ = 1 := by
  simpa [hM.1, hM.2] using toBlocks₂₂_mul_transpose_sub M

/-- The upper-left block of an element of the Siegel parabolic subgroup with multiplier one, as an
invertible matrix with inverse the transposed lower-right block. -/
private def upperLeftFun (M : siegelParabolicOne l S) : GL l S where
  val := (M : GL (l ⊕ l) S).val.toBlocks₁₁
  inv := (M : GL (l ⊕ l) S).val.toBlocks₂₂ᵀ
  val_inv := by
    rw [← transpose_transpose ((M : GL (l ⊕ l) S).val.toBlocks₁₁), ← transpose_mul,
      toBlocks₂₂_mul_transpose_toBlocks₁₁ M.property, transpose_one]
  inv_val := mul_eq_one_comm.mp <| by
    rw [← transpose_transpose ((M : GL (l ⊕ l) S).val.toBlocks₁₁), ← transpose_mul,
      toBlocks₂₂_mul_transpose_toBlocks₁₁ M.property, transpose_one]

variable (l S) in
/-- **The upper-left block** `(A B; 0 D) ↦ A`, a homomorphism from the Siegel parabolic subgroup
with multiplier one to `GL(l, S)`. Its kernel is the unipotent radical
(`TauCeti.GLSymplecticSimilitude.ker_upperLeft`). -/
def upperLeft : siegelParabolicOne l S →* GL l S where
  toFun := upperLeftFun
  map_one' := by
    ext i j
    simp [upperLeftFun, toBlocks₁₁, Matrix.one_apply]
  map_mul' M N := by
    ext : 1
    simp [upperLeftFun, toBlocks₁₁_mul, N.property.1]

/-- The matrix underlying `upperLeft M` is the upper-left block of `M`. -/
@[simp]
theorem coe_upperLeft (M : siegelParabolicOne l S) :
    (upperLeft l S M : Matrix l l S) =
      ((M : GLSymplecticSimilitude l S) : GL (l ⊕ l) S).val.toBlocks₁₁ :=
  (rfl)

/-- **The kernel of the upper-left block is the unipotent radical.** On the Siegel parabolic
subgroup with multiplier one, `A = 1` forces `D = 1` because `D Aᵀ = 1`. -/
theorem ker_upperLeft :
    (upperLeft l S).ker = (siegelUnipotent l S).subgroupOf (siegelParabolicOne l S) := by
  ext M
  rw [MonoidHom.mem_ker, Subgroup.mem_subgroupOf, mem_siegelUnipotent_iff, ← Units.val_inj,
    coe_upperLeft, Units.val_one]
  refine ⟨fun h => ⟨h, M.property.1, ?_⟩, fun h => h.1⟩
  simpa [h] using toBlocks₂₂_mul_transpose_toBlocks₁₁ M.property

/-- The unipotent radical is normal in the Siegel parabolic subgroup with multiplier one. -/
instance normal_siegelUnipotent_subgroupOf :
    ((siegelUnipotent l S).subgroupOf (siegelParabolicOne l S)).Normal :=
  ker_upperLeft (l := l) (S := S) ▸ MonoidHom.normal_ker _

/-- The Levi embedding `A ↦ diag(A, (A⁻¹)ᵀ)` lands in the Siegel parabolic subgroup with
multiplier one. -/
theorem leviHom_mem_siegelParabolicOne (A : GL l S) :
    (⟨GLSymplectic.leviHom A, GLSymplectic_le (GLSymplectic.leviHom A).property⟩ :
      GLSymplecticSimilitude l S) ∈ siegelParabolicOne l S :=
  ⟨by simp, multiplier_eq_one_of_mem (GLSymplectic.leviHom A).property⟩

/-- **The upper-left block is surjective**, split by the Levi embedding. -/
theorem upperLeft_surjective : Function.Surjective (upperLeft l S) := fun A =>
  ⟨⟨_, leviHom_mem_siegelParabolicOne A⟩, Units.ext (by simp)⟩

end Siegel

/-! ### The level subgroups -/

section Level

variable (l) (f : R →+* S)

/-- The **principal level subgroup** `Γ(f)`: the similitudes reducing to the identity, the kernel
of the map `GSp(l ⊕ l, R) → GSp(l ⊕ l, S)` induced by `f`. -/
def Gamma : Subgroup (GLSymplecticSimilitude l R) :=
  (map l f).ker

/-- `Γ(f)` is normal in `GSp(l ⊕ l, R)`, being a kernel. -/
instance normal_Gamma : (Gamma l f).Normal :=
  MonoidHom.normal_ker _

/-- The **level subgroup** `Γ₁(f)`: the similitudes reducing to `(1 ∗; 0 1)`. -/
def Gamma1 : Subgroup (GLSymplecticSimilitude l R) :=
  (siegelUnipotent l S).comap (map l f)

variable {l f}

/-- Membership in `Γ(f)`: the entrywise reduction is the identity matrix. -/
theorem mem_Gamma_iff {M : GLSymplecticSimilitude l R} :
    M ∈ Gamma l f ↔ (M : GL (l ⊕ l) R).val.map f = 1 := by
  rw [Gamma, MonoidHom.mem_ker, ← OneMemClass.coe_eq_one, ← Units.val_eq_one, coe_map,
    GeneralLinearGroup.val_map_apply]

/-- `γ ∈ Γ₁(f)` exactly when its reduction lies in the unipotent radical over `S`. -/
theorem mem_Gamma1_iff_map_mem {M : GLSymplecticSimilitude l R} :
    M ∈ Gamma1 l f ↔ map l f M ∈ siegelUnipotent l S := by
  rw [Gamma1, Subgroup.mem_comap]

/-- Membership in `Γ₁(f)`: `f(A) = 1`, `f(C) = 0` and `f(D) = 1`. -/
theorem mem_Gamma1_iff {M : GLSymplecticSimilitude l R} :
    M ∈ Gamma1 l f ↔ (M : GL (l ⊕ l) R).val.toBlocks₁₁.map f = 1 ∧
      (M : GL (l ⊕ l) R).val.toBlocks₂₁.map f = 0 ∧
      (M : GL (l ⊕ l) R).val.toBlocks₂₂.map f = 1 := by
  rw [mem_Gamma1_iff_map_mem, mem_siegelUnipotent_iff, coe_map, GeneralLinearGroup.val_map_apply,
    toBlocks₁₁_map, toBlocks₂₁_map, toBlocks₂₂_map]

variable (l f)

/-- `Γ(f) ≤ Γ₁(f)`. -/
theorem Gamma_le_Gamma1 : Gamma l f ≤ Gamma1 l f := fun M hM => by
  rw [Gamma, MonoidHom.mem_ker] at hM
  rw [Gamma1, Subgroup.mem_comap, hM]
  exact (siegelUnipotent l S).one_mem

variable {T : Type*} [CommRing T] (g : S →+* T)

/-- `Γ(f) ≤ Γ(g ∘ f)`: the principal level subgroup grows when the reduction is followed by
another ring homomorphism. For `ℤ_p → ℤ/pⁿ → ℤ/pᵐ` this is `Γ(pⁿ) ≤ Γ(pᵐ)` for `m ≤ n`. -/
theorem Gamma_le_Gamma_comp : Gamma l f ≤ Gamma l (g.comp f) := by
  rw [Gamma, Gamma, map_comp]
  exact fun M hM => by rw [MonoidHom.mem_ker] at hM ⊢; rw [MonoidHom.comp_apply, hM, map_one]

/-- `Γ₁(f) ≤ Γ₁(g ∘ f)`. -/
theorem Gamma1_le_Gamma1_comp : Gamma1 l f ≤ Gamma1 l (g.comp f) := by
  rw [Gamma1, Gamma1, map_comp, ← Subgroup.comap_comap]
  exact Subgroup.comap_mono (siegelUnipotent_le_comap_map g)

/-- Over a zero target ring, `Γ(f)` is everything; for `ℤ_p → ℤ/p⁰` this is `Γ(1) = GSp`. -/
theorem Gamma_eq_top [Subsingleton S] : Gamma l f = ⊤ :=
  eq_top_iff.2 fun _ _ => Subsingleton.elim _ _

/-- Over a zero target ring, `Γ₁(f)` is everything. -/
theorem Gamma1_eq_top [Subsingleton S] : Gamma1 l f = ⊤ := by
  rw [Gamma1, siegelUnipotent_eq_top, Subgroup.comap_top]

variable [Nonempty l]

/-- The **level subgroup** `Γ₀(f)`: the similitudes `(A B; C D)` with `f(C) = 0` and
`f(c(γ)) = 1`. -/
def Gamma0 : Subgroup (GLSymplecticSimilitude l R) :=
  (siegelParabolicOne l S).comap (map l f)

variable {l f}

/-- `γ ∈ Γ₀(f)` exactly when its reduction lies in the Siegel parabolic subgroup with multiplier
one over `S`. -/
theorem mem_Gamma0_iff_map_mem {M : GLSymplecticSimilitude l R} :
    M ∈ Gamma0 l f ↔ map l f M ∈ siegelParabolicOne l S := by
  rw [Gamma0, Subgroup.mem_comap]

/-- Membership in `Γ₀(f)`: `f(C) = 0` and `f(c(γ)) = 1`. -/
theorem mem_Gamma0_iff {M : GLSymplecticSimilitude l R} :
    M ∈ Gamma0 l f ↔ (M : GL (l ⊕ l) R).val.toBlocks₂₁.map f = 0 ∧
      f (multiplier l R M : R) = 1 := by
  rw [mem_Gamma0_iff_map_mem, mem_siegelParabolicOne_iff, multiplier_map, ← Units.val_eq_one,
    Units.coe_map, MonoidHom.coe_ofClass, coe_map, GeneralLinearGroup.val_map_apply,
    toBlocks₂₁_map]

variable (l f)

/-- `Γ₁(f) ≤ Γ₀(f)`. -/
theorem Gamma1_le_Gamma0 : Gamma1 l f ≤ Gamma0 l f :=
  Subgroup.comap_mono (siegelUnipotent_le_siegelParabolicOne l S)

/-- `Γ₀(f) ≤ Γ₀(g ∘ f)`. -/
theorem Gamma0_le_Gamma0_comp : Gamma0 l f ≤ Gamma0 l (g.comp f) := by
  rw [Gamma0, Gamma0, map_comp, ← Subgroup.comap_comap]
  exact Subgroup.comap_mono (siegelParabolicOne_le_comap_map g)

/-- Over a zero target ring, `Γ₀(f)` is everything. -/
theorem Gamma0_eq_top [Subsingleton S] : Gamma0 l f = ⊤ := by
  rw [Gamma0, siegelParabolicOne_eq_top, Subgroup.comap_top]

namespace Gamma0

/-- **The reduced upper-left block** `γ ↦ f(A)` on `Γ₀(f)`, a homomorphism to `GL(l, S)` with
kernel `Γ₁(f)` (`TauCeti.GLSymplecticSimilitude.Gamma0.ker_upperLeft`). -/
noncomputable def upperLeft : Gamma0 l f →* GL l S :=
  (GLSymplecticSimilitude.upperLeft l S).comp
    (((map l f).comp (Gamma0 l f).subtype).codRestrict _ fun M =>
      mem_Gamma0_iff_map_mem.1 M.property)

variable {l f}

/-- The matrix underlying `upperLeft f γ` is the reduction of the upper-left block of `γ`. -/
@[simp]
theorem coe_upperLeft (M : Gamma0 l f) :
    (upperLeft l f M : Matrix l l S) =
      ((M : GLSymplecticSimilitude l R) : GL (l ⊕ l) R).val.toBlocks₁₁.map f := by
  simp [upperLeft]

variable (l f)

/-- **The kernel of the reduced upper-left block is `Γ₁(f)`.** -/
theorem ker_upperLeft : (upperLeft l f).ker = (Gamma1 l f).subgroupOf (Gamma0 l f) := by
  ext M
  rw [Subgroup.mem_subgroupOf, mem_Gamma1_iff_map_mem, upperLeft, MonoidHom.mem_ker,
    MonoidHom.comp_apply, ← MonoidHom.mem_ker, GLSymplecticSimilitude.ker_upperLeft,
    Subgroup.mem_subgroupOf, MonoidHom.codRestrict_apply]
  simp

/-- `Γ₁(f)` is normal in `Γ₀(f)`. -/
instance normal_Gamma1_subgroupOf : ((Gamma1 l f).subgroupOf (Gamma0 l f)).Normal :=
  ker_upperLeft l f ▸ MonoidHom.normal_ker _

/-- **The reduced upper-left block is surjective** when `f` is surjective and reflects units, as
for reduction `ℤ_p → ℤ/pᵐ`: a lift of `A` to `GL(l, R)` gives the Levi element
`diag(Ã, (Ã⁻¹)ᵀ) ∈ Γ₀(f)`. -/
theorem upperLeft_surjective [IsLocalHom f] (hf : Function.Surjective f) :
    Function.Surjective (upperLeft l f) := by
  intro A
  obtain ⟨B, rfl⟩ := Matrix.GeneralLinearGroup.map_surjective f hf A
  have hB := leviHom_mem_siegelParabolicOne B
  refine ⟨⟨_, mem_Gamma0_iff_map_mem.2 (siegelParabolicOne_le_comap_map f hB)⟩, Units.ext ?_⟩
  ext i j
  simp [Matrix.GeneralLinearGroup.map_apply]

/-- **`Γ₀(f)/Γ₁(f) ≃* GL(l, S)`** through the reduced upper-left block, when `f` is surjective and
reflects units. -/
noncomputable def quotientEquiv [IsLocalHom f] (hf : Function.Surjective f) :
    Gamma0 l f ⧸ (Gamma1 l f).subgroupOf (Gamma0 l f) ≃* GL l S :=
  (QuotientGroup.quotientMulEquivOfEq (ker_upperLeft l f).symm).trans
    (QuotientGroup.quotientKerEquivOfSurjective _ (upperLeft_surjective l f hf))

end Gamma0

end Level

end GLSymplecticSimilitude

end TauCeti
