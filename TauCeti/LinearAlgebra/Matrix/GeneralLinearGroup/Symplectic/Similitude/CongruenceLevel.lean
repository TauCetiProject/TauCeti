/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.LinearAlgebra.Matrix.GeneralLinearGroup.Symplectic.Similitude.SiegelParabolic
-- `PadicInt.toZModPow` occurs in the statements of the `p`-adic specialization.
public import Mathlib.NumberTheory.Padics.RingHoms
-- `QuotientGroup.quotientKerEquivOfSurjective` gives the quotient `Γ₀ / Γ₁ ≃* GL`.
public import Mathlib.GroupTheory.QuotientGroup.Basic
-- Non-public, used only in the proofs: blocks of the identity and of entrywise images, the Levi
-- embedding used to lift the upper-left block, lifting invertible matrices along a local ring
-- hom, and the locality of truncation modulo `p ^ m`.
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
(`TauCeti.GSp.siegelParabolic`), on which the upper-left block `A` is a group morphism to `GL`
(`TauCeti.GSp.upperLeftHom`). Its composite with reduction, `TauCeti.GSp.Gamma0.upperLeftHom`,
has kernel `Γ₁(f)`, because a block upper-triangular similitude satisfies `A Dᵀ = c • 1`, so
`A = 1` and `c = 1` force `D = 1`.
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

* `TauCeti.GSp.Gamma`, `TauCeti.GSp.Gamma1`, `TauCeti.GSp.Gamma0`: the level subgroups.
* `TauCeti.GSp.Gamma0.upperLeftHom`: the upper-left block of the reduction, on `Γ₀(f)`.
* `TauCeti.GSp.Gamma0.quotientGamma1EquivGL`: the isomorphism `Γ₀(f) / Γ₁(f) ≃* GL l S`.

## Main results

* `TauCeti.GSp.mem_Gamma_iff`, `TauCeti.GSp.mem_Gamma1_iff`, `TauCeti.GSp.mem_Gamma0_iff`: the
  congruence conditions.
* `TauCeti.GSp.Gamma_le_Gamma1`, `TauCeti.GSp.Gamma1_le_Gamma0`: `Γ(f) ⊆ Γ₁(f) ⊆ Γ₀(f)`.
* `TauCeti.GSp.Gamma.normal`, `TauCeti.GSp.Gamma0.normal_Gamma1`: the two normalities.
* `TauCeti.GSp.Gamma0.mem_ker_upperLeftHom_iff`: the kernel of the upper-left block on `Γ₀(f)`
  consists of the elements whose reduction has upper-left block `1`.
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

/-! ### The level subgroups -/

variable (l) {R : Type u} [CommRing R] {S : Type v} [CommRing S]

/-- The **principal congruence subgroup** `Γ(f)`: the kernel of reduction along `f`. For
`f = PadicInt.toZModPow m` this is `Γ(pᵐ) = {γ : γ ≡ 1 mod pᵐ}`. -/
def Gamma (f : R →+* S) : Subgroup (GSp l R) :=
  (map l f).ker

variable {l}

/-- Membership in `Γ(f)`: the reduction is the identity matrix. -/
@[simp]
theorem mem_Gamma_iff {f : R →+* S} {M : GSp l R} :
    M ∈ Gamma l f ↔ ((M : GL (l ⊕ l) R) : Matrix (l ⊕ l) (l ⊕ l) R).map f = 1 := by
  simp [Gamma, ← Subtype.coe_inj, Units.ext_iff]

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
upper-triangular with multiplier `1`. For `f = PadicInt.toZModPow m` this is
`Γ₀(pᵐ) = {γ : γ ≡ (∗ ∗; 0 ∗) mod pᵐ and c(γ) ≡ 1 mod pᵐ}`, Scholze's `Γ₀(pᵐ)`
(Definition 3.1.1) with the similitude condition `c(γ) ≡ 1 mod pᵐ` in place of the printed
`det γ ≡ 1 mod pᵐ`. -/
noncomputable def Gamma0 (f : R →+* S) : Subgroup (GSp l R) :=
  (siegelParabolic l S).comap (map l f) ⊓ ((Units.map (f : R →* S)).comp (multiplier l R)).ker

/-- Membership in `Γ₀(f)`: the reduction has vanishing lower-left block and the multiplier
reduces to `1`. -/
@[simp]
theorem mem_Gamma0_iff {f : R →+* S} {M : GSp l R} :
    M ∈ Gamma0 l f ↔
      ((M : GL (l ⊕ l) R) : Matrix (l ⊕ l) (l ⊕ l) R).toBlocks₂₁.map f = 0 ∧
        f (multiplier l R M : R) = 1 := by
  simp [Gamma0, Units.ext_iff]

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
      ((M : GSp l R) : GL (l ⊕ l) R).val.toBlocks₁₁.map f := by
  simp [upperLeftHom]

/-- `γ ∈ Γ₀(f)` lies in the kernel of the upper-left block of the reduction exactly when that
block is the identity. -/
theorem mem_ker_upperLeftHom_iff {f : R →+* S} {M : Gamma0 l f} :
    M ∈ (upperLeftHom l f).ker ↔
      ((M : GSp l R) : GL (l ⊕ l) R).val.toBlocks₁₁.map f = 1 := by
  rw [MonoidHom.mem_ker, Units.ext_iff, coe_upperLeftHom, Units.val_one]

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
@[simp]
theorem mem_Gamma1_iff {f : R →+* S} {M : GSp l R} :
    M ∈ Gamma1 l f ↔
      ((M : GL (l ⊕ l) R) : Matrix (l ⊕ l) (l ⊕ l) R).toBlocks₁₁.map f = 1 ∧
        ((M : GL (l ⊕ l) R) : Matrix (l ⊕ l) (l ⊕ l) R).toBlocks₂₁.map f = 0 ∧
          ((M : GL (l ⊕ l) R) : Matrix (l ⊕ l) (l ⊕ l) R).toBlocks₂₂.map f = 1 := by
  have hAD (N : GSp l R)
      (h : ((N : GL (l ⊕ l) R) : Matrix (l ⊕ l) (l ⊕ l) R).toBlocks₂₁.map f = 0) :
      ((N : GL (l ⊕ l) R) : Matrix (l ⊕ l) (l ⊕ l) R).toBlocks₁₁.map f *
          (((N : GL (l ⊕ l) R) : Matrix (l ⊕ l) (l ⊕ l) R).toBlocks₂₂.map f)ᵀ =
        f (multiplier l R N : R) • 1 := by
    simpa using toBlocks₁₁_mul_transpose_toBlocks₂₂_of_toBlocks₂₁_eq_zero (M := map l f N)
      (by simpa using h)
  constructor
  · rintro ⟨M, hM, rfl⟩
    have h₁₁ := Gamma0.mem_ker_upperLeftHom_iff.1 hM
    obtain ⟨h₂₁, hc⟩ := mem_Gamma0_iff.1 M.property
    refine ⟨h₁₁, h₂₁, ?_⟩
    have := hAD M h₂₁
    rw [h₁₁, Matrix.one_mul, hc, one_smul] at this
    simpa using congrArg Matrix.transpose this
  · rintro ⟨h₁₁, h₂₁, h₂₂⟩
    have hc : f (multiplier l R M : R) = 1 := by
      have := hAD M h₂₁
      rw [h₁₁, h₂₂, transpose_one, Matrix.one_mul] at this
      exact scalar_inj.1 (by simpa [smul_one_eq_diagonal] using this.symm)
    exact ⟨⟨M, mem_Gamma0_iff.2 ⟨h₂₁, hc⟩⟩, Gamma0.mem_ker_upperLeftHom_iff.2 h₁₁, rfl⟩

/-- `Γ(f) ⊆ Γ₁(f)`. -/
theorem Gamma_le_Gamma1 (f : R →+* S) : Gamma l f ≤ Gamma1 l f := by
  intro M hM
  rw [mem_Gamma_iff] at hM
  simp only [mem_Gamma1_iff, ← toBlocks₁₁_map, ← toBlocks₂₁_map, ← toBlocks₂₂_map, hM]
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
    rw [mem_Gamma0_iff, hL, hc, Units.val_one, map_one, toBlocks_fromBlocks₂₁]
    simp
  refine ⟨⟨L, hL0⟩, Units.ext ?_⟩
  rw [coe_upperLeftHom, Matrix.GeneralLinearGroup.val_map_apply, hL, toBlocks_fromBlocks₁₁]

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
    quotientGamma1EquivGL l hf (QuotientGroup.mk M) = upperLeftHom l f M := by
  rw [quotientGamma1EquivGL, MulEquiv.trans_apply, QuotientGroup.quotientMulEquivOfEq_mk,
    QuotientGroup.quotientKerEquivOfSurjective,
    QuotientGroup.quotientKerEquivOfRightInverse_apply, QuotientGroup.kerLift_mk]

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
  simp [← Matrix.map_map, h₂₁, hc]

/-- A factorization `f' = g ∘ f` gives `Γ₁(f) ⊆ Γ₁(f')`. -/
theorem Gamma1_le_of_comp {T : Type*} [CommRing T] {f : R →+* S} {f' : R →+* T} (g : S →+* T)
    (h : g.comp f = f') : Gamma1 l f ≤ Gamma1 l f' := by
  intro M hM
  rw [mem_Gamma1_iff] at hM ⊢
  obtain ⟨h₁₁, h₂₁, h₂₂⟩ := hM
  subst h
  simp [← Matrix.map_map, h₁₁, h₂₁, h₂₂]

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
