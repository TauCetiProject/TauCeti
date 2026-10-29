/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.Algebra.Homology.DG.Bimodule.Hom.Complex
public import TauCeti.Algebra.Homology.DG.Module.Right.Composition

/-!
# Composition of homogeneous DG bimodule maps

Signed left-linear, right-linear homogeneous cochains are closed under composition. Their
composition is the existing right-module composition, restricted to signed left-linear maps.
The signs multiply to the sign of the sum of the degrees. The differential satisfies Keller's
Leibniz rule `δ(g ∘ f) = δ(g) ∘ f + (-1)^|g| g ∘ δ(f)`, and the identity cochain is closed.
These operations give the Hom complexes of DG bimodules their associative, unital composition.

The construction uses `dgRightModuleCochains.comp` and its differential and identity laws.

## References

* B. Keller, *Deriving DG categories*, Sections 2 and 6.1.
-/

public section

namespace TauCeti.dgBimoduleCochains

universe uR uA uB uM uN uP uQ

variable {R : Type uR} {A : Type uA} {B : Type uB}
  {M : Type uM} {N : Type uN} {P : Type uP}
  [CommRing R] [Ring A] [Ring B] [Algebra R A] [Algebra R B]
  [AddCommGroup M] [Module R M] [Module A M] [Module Bᵐᵒᵖ M]
  [IsScalarTower R Bᵐᵒᵖ M]
  [AddCommGroup N] [Module R N] [Module A N] [Module Bᵐᵒᵖ N]
  [IsScalarTower R A N] [IsScalarTower R Bᵐᵒᵖ N]
  [AddCommGroup P] [Module R P] [Module A P] [Module Bᵐᵒᵖ P]
  [IsScalarTower R A P] [IsScalarTower R Bᵐᵒᵖ P]
  {𝒜 : ℤ → Submodule R A}
  {ℳ : ℤ → Submodule R M} {𝒩 : ℤ → Submodule R N} {ℳP : ℤ → Submodule R P}

/-- Composition of homogeneous signed bimodule cochains, in Keller's order. -/
def comp {p q j : ℤ}
    (g : dgBimoduleCochains (B := B) (𝒜 := 𝒜) (ℳ := 𝒩) (𝒩 := ℳP) p)
    (f : dgBimoduleCochains (B := B) (𝒜 := 𝒜) (ℳ := ℳ) (𝒩 := 𝒩) q)
    (hpq : p + q = j) :
    dgBimoduleCochains (B := B) (𝒜 := 𝒜) (ℳ := ℳ) (𝒩 := ℳP) j :=
  ⟨dgRightModuleCochains.comp g.1 f.1 hpq, by
    subst j
    apply mem_iff.mpr
    intro r a ha x
    rw [dgRightModuleCochains.comp_apply, map_smul_left f ha, map_zsmul_unit,
      map_smul_left g ha, smul_smul, ← Int.negOnePow_add, ← add_mul]
    rw [add_comm q p, dgRightModuleCochains.comp_apply]⟩

/-- Forgetting left linearity preserves composition. -/
@[simp]
theorem comp_val {p q j : ℤ}
    (g : dgBimoduleCochains (B := B) (𝒜 := 𝒜) (ℳ := 𝒩) (𝒩 := ℳP) p)
    (f : dgBimoduleCochains (B := B) (𝒜 := 𝒜) (ℳ := ℳ) (𝒩 := 𝒩) q)
    (hpq : p + q = j) :
    (comp g f hpq).1 = dgRightModuleCochains.comp g.1 f.1 hpq := (rfl)

/-- Bimodule cochain composition is pointwise composition. -/
@[simp↓]
theorem comp_apply {p q j : ℤ}
    (g : dgBimoduleCochains (B := B) (𝒜 := 𝒜) (ℳ := 𝒩) (𝒩 := ℳP) p)
    (f : dgBimoduleCochains (B := B) (𝒜 := 𝒜) (ℳ := ℳ) (𝒩 := 𝒩) q)
    (hpq : p + q = j) (x : M) :
    (comp g f hpq).1.1 x = g.1.1 (f.1.1 x) := by
  rw [comp_val, dgRightModuleCochains.comp_apply]

@[simp]
theorem add_comp {p q j : ℤ}
    (g g' : dgBimoduleCochains (B := B) (𝒜 := 𝒜) (ℳ := 𝒩) (𝒩 := ℳP) p)
    (f : dgBimoduleCochains (B := B) (𝒜 := 𝒜) (ℳ := ℳ) (𝒩 := 𝒩) q)
    (hpq : p + q = j) : comp (g + g') f hpq = comp g f hpq + comp g' f hpq := by
  apply Subtype.ext
  simp

@[simp]
theorem comp_add {p q j : ℤ}
    (g : dgBimoduleCochains (B := B) (𝒜 := 𝒜) (ℳ := 𝒩) (𝒩 := ℳP) p)
    (f f' : dgBimoduleCochains (B := B) (𝒜 := 𝒜) (ℳ := ℳ) (𝒩 := 𝒩) q)
    (hpq : p + q = j) : comp g (f + f') hpq = comp g f hpq + comp g f' hpq := by
  apply Subtype.ext
  simp

@[simp]
theorem smul_comp {p q j : ℤ} (r : R)
    (g : dgBimoduleCochains (B := B) (𝒜 := 𝒜) (ℳ := 𝒩) (𝒩 := ℳP) p)
    (f : dgBimoduleCochains (B := B) (𝒜 := 𝒜) (ℳ := ℳ) (𝒩 := 𝒩) q)
    (hpq : p + q = j) : comp (r • g) f hpq = r • comp g f hpq := by
  apply Subtype.ext
  simp

@[simp]
theorem comp_smul {p q j : ℤ} (r : R)
    (g : dgBimoduleCochains (B := B) (𝒜 := 𝒜) (ℳ := 𝒩) (𝒩 := ℳP) p)
    (f : dgBimoduleCochains (B := B) (𝒜 := 𝒜) (ℳ := ℳ) (𝒩 := 𝒩) q)
    (hpq : p + q = j) : comp g (r • f) hpq = r • comp g f hpq := by
  apply Subtype.ext
  simp

@[simp]
theorem zero_comp {p q j : ℤ}
    (f : dgBimoduleCochains (B := B) (𝒜 := 𝒜) (ℳ := ℳ) (𝒩 := 𝒩) q)
    (hpq : p + q = j) :
    comp (0 : dgBimoduleCochains (B := B) (𝒜 := 𝒜) (ℳ := 𝒩) (𝒩 := ℳP) p) f hpq = 0 := by
  apply Subtype.ext
  simp

@[simp]
theorem comp_zero {p q j : ℤ}
    (g : dgBimoduleCochains (B := B) (𝒜 := 𝒜) (ℳ := 𝒩) (𝒩 := ℳP) p)
    (hpq : p + q = j) :
    comp g (0 : dgBimoduleCochains (B := B) (𝒜 := 𝒜) (ℳ := ℳ) (𝒩 := 𝒩) q) hpq = 0 := by
  apply Subtype.ext
  simp

variable [IsScalarTower R A M]

/-- The degree-zero identity bimodule cochain. -/
def id : dgBimoduleCochains (B := B) (𝒜 := 𝒜) (ℳ := ℳ) (𝒩 := ℳ) 0 :=
  ⟨dgRightModuleCochains.id, by simp⟩

@[simp]
theorem id_val :
    (id (B := B) (𝒜 := 𝒜) (ℳ := ℳ)).1 = dgRightModuleCochains.id := (rfl)

/-- The degree-zero identity bimodule cochain acts as the identity map. -/
@[simp↓]
theorem id_apply (x : M) : (id (B := B) (𝒜 := 𝒜) (ℳ := ℳ)).1.1 x = x := by
  rw [id_val, dgRightModuleCochains.id_apply]

/-- Composing on the right with the identity bimodule cochain leaves the cochain unchanged. -/
@[simp]
theorem comp_id {p : ℤ}
    (f : dgBimoduleCochains (B := B) (𝒜 := 𝒜) (ℳ := ℳ) (𝒩 := 𝒩) p) :
    comp f (id (B := B) (𝒜 := 𝒜) (ℳ := ℳ)) (add_zero p) = f := by
  apply Subtype.ext
  simp

omit [IsScalarTower R A M] in
/-- Composing on the left with the identity bimodule cochain leaves the cochain unchanged. -/
@[simp]
theorem id_comp {p : ℤ}
    (f : dgBimoduleCochains (B := B) (𝒜 := 𝒜) (ℳ := ℳ) (𝒩 := 𝒩) p) :
    comp (id (B := B) (𝒜 := 𝒜) (ℳ := 𝒩)) f (zero_add p) = f := by
  apply Subtype.ext
  simp

omit [IsScalarTower R A M] in
/-- Composition of homogeneous bimodule cochains is associative. -/
@[simp]
theorem comp_assoc {Q : Type uQ} [AddCommGroup Q] [Module R Q] [Module A Q] [Module Bᵐᵒᵖ Q]
    [IsScalarTower R A Q] [IsScalarTower R Bᵐᵒᵖ Q] {ℳQ : ℤ → Submodule R Q}
    {r p q j : ℤ}
    (k : dgBimoduleCochains (B := B) (𝒜 := 𝒜) (ℳ := ℳP) (𝒩 := ℳQ) r)
    (g : dgBimoduleCochains (B := B) (𝒜 := 𝒜) (ℳ := 𝒩) (𝒩 := ℳP) p)
    (f : dgBimoduleCochains (B := B) (𝒜 := 𝒜) (ℳ := ℳ) (𝒩 := 𝒩) q)
    (hrpq : (r + p) + q = j) :
    comp (comp k g rfl) f hrpq = comp k (comp g f rfl) (by omega) := by
  apply Subtype.ext
  simp only [comp_val, dgRightModuleCochains.comp_assoc]

variable {ℬ : ℤ → Submodule R B} [GradedAlgebra 𝒜] [GradedAlgebra ℬ]
  {dA : A →ₗ[R] A} {dB : B →ₗ[R] B}
  {hA : IsDGAlgebra 𝒜 dA} {hB : IsDGAlgebra ℬ dB}
  [SMulCommClass A Bᵐᵒᵖ M] [SMulCommClass A Bᵐᵒᵖ N] [SMulCommClass A Bᵐᵒᵖ P]
  [DirectSum.Decomposition ℳ] [DirectSum.Decomposition 𝒩] [DirectSum.Decomposition ℳP]
  [SetLike.GradedSMul 𝒜 ℳ] [SetLike.GradedSMul 𝒜 𝒩] [SetLike.GradedSMul 𝒜 ℳP]
  [SetLike.GradedSMul (InternalGrading.ofDecomposition ℬ).opposite.piece ℳ]
  [SetLike.GradedSMul (InternalGrading.ofDecomposition ℬ).opposite.piece 𝒩]
  [SetLike.GradedSMul (InternalGrading.ofDecomposition ℬ).opposite.piece ℳP]
  {dM : M →ₗ[R] M} {dN : N →ₗ[R] N} {dP : P →ₗ[R] P}
  {hM : IsDGBimodule hA hB ℳ dM} {hN : IsDGBimodule hA hB 𝒩 dN}
  {hP : IsDGBimodule hA hB ℳP dP}

/-- The graded Leibniz rule for composition of bimodule cochains. -/
theorem differential_comp {p q : ℤ}
    (g : dgBimoduleCochains (B := B) (𝒜 := 𝒜) (ℳ := 𝒩) (𝒩 := ℳP) p)
    (f : dgBimoduleCochains (B := B) (𝒜 := 𝒜) (ℳ := ℳ) (𝒩 := 𝒩) q) :
    differential (hM := hM) (hN := hP) (p + q) (comp g f rfl) =
      comp (differential (hM := hN) (hN := hP) p g) f (by omega) +
        p.negOnePow • comp g (differential (hM := hM) (hN := hN) q f) (by omega) := by
  apply Subtype.ext
  simpa only [differential_val, comp_val, Submodule.coe_add, Submodule.coe_smul_of_tower] using
    dgRightModuleCochains.differential_comp
      (hM := hM.isDGRightModule) (hN := hN.isDGRightModule) (hP := hP.isDGRightModule) g.1 f.1

/-- The identity bimodule cochain is closed. -/
@[simp]
theorem differential_id (hM : IsDGBimodule hA hB ℳ dM) :
    differential (hM := hM) (hN := hM) 0 (id (B := B) (𝒜 := 𝒜) (ℳ := ℳ)) = 0 := by
  apply Subtype.ext
  simp only [differential_val, id_val, dgRightModuleCochains.differential_id, Submodule.coe_zero]

end TauCeti.dgBimoduleCochains
