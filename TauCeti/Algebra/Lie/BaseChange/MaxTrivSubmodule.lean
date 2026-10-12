/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import Mathlib.Algebra.Lie.Abelian
public import Mathlib.Algebra.Lie.BaseChange
public import Mathlib.RingTheory.Flat.Basic
import Mathlib.LinearAlgebra.TensorProduct.Pi
import TauCeti.LinearAlgebra.TensorProduct.Kernel

/-!
# Invariant vectors under extension of scalars

For a Lie module `M` over a Lie algebra `L` over a commutative ring `R`, the invariant vectors form
the Lie submodule `LieModule.maxTrivSubmodule R L M`. This file compares the invariants of the
extension of scalars `A ⊗[R] M`, as a module over `A ⊗[R] L`, with the extension of the
invariants of `M`:

```text
maxTrivSubmodule A (A ⊗[R] L) (A ⊗[R] M) = (maxTrivSubmodule R L M).baseChange A.
```

The containment `⊇` holds for every coefficient algebra. The reverse containment holds when `A` is
flat over `R` and `L` is finitely generated as an `R`-module: the invariants are then the kernel
of the linear map `m ↦ (⁅s i, m⁆)ᵢ` for a finite spanning family `s` of `L`, and a flat extension
of scalars commutes with kernels (`LinearMap.ker_baseChange_of_flat`).

The equality is what lets an invariant vector found after extending scalars be traded for one over
the original ring: if every invariant vector of `M` lies in a submodule `N`, then every invariant
vector of `A ⊗[R] M` lies in `N.baseChange A`. Weyl's complete reducibility theorem over a field
of characteristic zero is descended from the algebraically closed case in exactly this way.

## Main results

* `LieModule.baseChange_maxTrivSubmodule_le`: the extension of an invariant vector is invariant.
* `LieModule.maxTrivSubmodule_baseChange`: over a flat coefficient algebra, and for a finitely
  generated Lie algebra, the invariants of the extension are the extension of the invariants.
-/

public section

open TensorProduct

namespace LieModule

variable (R A L M : Type*) [CommRing R] [CommRing A] [Algebra R A]
  [LieRing L] [LieAlgebra R L]
  [AddCommGroup M] [Module R M] [LieRingModule L M] [LieModule R L M]

/-- **The extension of an invariant vector is invariant**, over any coefficient algebra. -/
theorem baseChange_maxTrivSubmodule_le :
    (maxTrivSubmodule R L M).baseChange A ≤ maxTrivSubmodule A (A ⊗[R] L) (A ⊗[R] M) := by
  rw [← LieSubmodule.toSubmodule_le_toSubmodule, LieSubmodule.coe_baseChange,
    Submodule.baseChange_eq_span, Submodule.span_le]
  rintro - ⟨m, hm, rfl⟩
  rw [SetLike.mem_coe, LieSubmodule.mem_toSubmodule, mem_maxTrivSubmodule]
  intro x
  induction x using TensorProduct.inductionOn with
  | tmul a y =>
    rw [TensorProduct.mk_apply, LieAlgebra.ExtendScalars.bracket_tmul,
      (mem_maxTrivSubmodule R L M m).1 hm y, tmul_zero]
  | add x y hx hy => rw [add_lie, hx, hy, add_zero]

/-- **Over a flat coefficient algebra, extension of scalars commutes with taking invariants**, for
a Lie algebra that is finitely generated as a module. -/
theorem maxTrivSubmodule_baseChange [Module.Flat R A] [Module.Finite R L] :
    maxTrivSubmodule A (A ⊗[R] L) (A ⊗[R] M) = (maxTrivSubmodule R L M).baseChange A := by
  refine le_antisymm (fun m hm ↦ ?_) (baseChange_maxTrivSubmodule_le R A L M)
  -- The invariants are the kernel of `φ : m ↦ (⁅s i, m⁆)ᵢ` for a finite spanning family `s`.
  obtain ⟨n, s, hs⟩ := Module.Finite.exists_fin (R := R) (M := L)
  let φ : M →ₗ[R] (Fin n → M) := LinearMap.pi fun i ↦ toEnd R L M (s i)
  have hker : LinearMap.ker φ = (maxTrivSubmodule R L M : Submodule R M) := by
    ext v
    simp only [LinearMap.mem_ker, LieSubmodule.mem_toSubmodule, mem_maxTrivSubmodule]
    refine ⟨fun hv x ↦ ?_, fun hv ↦ funext fun i ↦ hv (s i)⟩
    -- `x ↦ ⁅x, v⁆` is linear and vanishes on the spanning family `s`.
    have hext : (toEnd R L M : L →ₗ[R] Module.End R M).flip v = 0 :=
      LinearMap.ext_on_range hs fun i ↦ congrFun hv i
    exact LinearMap.congr_fun hext x
  -- After extending scalars, the components of `φ` become the actions of the `1 ⊗ₜ s i`.
  have hφ : φ.baseChange A m = 0 := by
    refine (piRight R A A fun _ : Fin n ↦ M).injective ?_
    rw [map_zero]
    funext i
    rw [mem_maxTrivSubmodule] at hm
    rw [Pi.zero_apply, ← hm (1 ⊗ₜ s i)]
    clear hm
    induction m using TensorProduct.inductionOn with
    | tmul a v =>
      simp [φ, LieAlgebra.ExtendScalars.bracket_tmul]
    | add v w hv hw => simp only [map_add, Pi.add_apply, lie_add, hv, hw]
  rw [← LieSubmodule.mem_toSubmodule, LieSubmodule.coe_baseChange, ← hker,
    ← LinearMap.ker_baseChange_of_flat]
  exact hφ

end LieModule
