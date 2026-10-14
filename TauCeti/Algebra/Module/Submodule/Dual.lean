/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.Algebra.Module.Submodule.Essential
public import TauCeti.Algebra.Module.Submodule.Superfluous
public import Mathlib.LinearAlgebra.Dual.Lemmas

/-!
# Essential and superfluous submodules under linear duality

For a finite-dimensional right module `M` over a `k`-algebra `A`, annihilation identifies its
submodule lattice with the opposite of the submodule lattice of its left dual. Consequently a
submodule is superfluous exactly when its annihilator is essential. This is the lattice
minimality comparison used to dualize projective covers and minimal projective presentations.

The dual action is specified by a linear equivalence `e : N ≃ₗ[k] Module.Dual k M` satisfying
`e (a • n) m = e n (op a • m)`. No competing global module instance on a linear-map type is
introduced. The annihilator constructions use Mathlib's `Submodule.dualAnnihilator` and
`Submodule.dualCoannihilator`; double annihilation uses their vector-space API.

## References

* I. Assem, D. Simson, A. Skowroński, *Elements of the Representation Theory of Associative
  Algebras*, Vol. 1, Sections I.4 and I.5.
* M. Auslander, I. Reiten, S. O. Smalø, *Representation Theory of Artin Algebras*, Section I.3.
-/

public section

namespace TauCeti

universe u v w t

section Semiring

variable {k : Type u} {A : Type v} {M : Type w} {N : Type t}
  [CommSemiring k] [Semiring A] [Algebra k A]
  [AddCommMonoid M] [Module Aᵐᵒᵖ M] [Module k M]
  [AddCommMonoid N] [Module A N] [Module k N]
  (e : N ≃ₗ[k] Module.Dual k M)
  (he : ∀ (a : A) (n : N) (m : M), e (a • n) m = e n (MulOpposite.op a • m))

section Annihilator

variable [IsScalarTower k Aᵐᵒᵖ M]

/-- The left submodule of the dual annihilating a right submodule. -/
def moduleDualAnnihilator (S : Submodule Aᵐᵒᵖ M) : Submodule A N where
  __ := ((S.restrictScalars k).dualAnnihilator.comap e.toLinearMap).toAddSubmonoid
  smul_mem' a n hn := (Submodule.mem_dualAnnihilator _).mpr fun m hm ↦
    (he a n m).trans ((Submodule.mem_dualAnnihilator _).mp hn _
      (S.smul_mem (MulOpposite.op a) hm))

/-- Membership in the module annihilator means vanishing on the given submodule. -/
@[simp]
theorem mem_moduleDualAnnihilator (S : Submodule Aᵐᵒᵖ M) (n : N) :
    n ∈ moduleDualAnnihilator e he S ↔ ∀ m ∈ S, e n m = 0 :=
  ⟨fun hn ↦ (Submodule.mem_dualAnnihilator _).mp hn,
    fun hn ↦ (Submodule.mem_dualAnnihilator _).mpr hn⟩

/-- Annihilation takes a sum of right submodules to the intersection of their annihilators. -/
@[simp]
theorem moduleDualAnnihilator_sup (S T : Submodule Aᵐᵒᵖ M) :
    moduleDualAnnihilator e he (S ⊔ T) =
      moduleDualAnnihilator e he S ⊓ moduleDualAnnihilator e he T := by
  ext n
  -- Use the defining carriers to avoid requiring a scalar tower on the target `N`.
  change n ∈ ((S ⊔ T).restrictScalars k).dualAnnihilator.comap e.toLinearMap ↔
    n ∈ (S.restrictScalars k).dualAnnihilator.comap e.toLinearMap ⊓
      (T.restrictScalars k).dualAnnihilator.comap e.toLinearMap
  rw [Submodule.restrictScalars_sup, Submodule.dualAnnihilator_sup_eq, Submodule.comap_inf]

/-- The annihilator of the zero submodule is the whole dual module. -/
@[simp]
theorem moduleDualAnnihilator_bot :
    moduleDualAnnihilator e he (⊥ : Submodule Aᵐᵒᵖ M) = ⊤ := by
  ext n
  simp

end Annihilator

section Coannihilator

variable [IsScalarTower k A N]

/-- The right submodule annihilated by a left submodule of the dual. -/
def moduleDualCoannihilator (T : Submodule A N) : Submodule Aᵐᵒᵖ M where
  __ := (((T.restrictScalars k).map e.toLinearMap).dualCoannihilator).toAddSubmonoid
  smul_mem' a m hm := (Submodule.mem_dualCoannihilator _).mpr <| by
    rintro _ ⟨n, hn, rfl⟩
    exact (he a.unop n m).symm.trans
      ((Submodule.mem_dualCoannihilator _).mp hm _ ⟨a.unop • n, T.smul_mem _ hn, rfl⟩)

/-- Membership in the module coannihilator means that every functional in the given
submodule vanishes on the vector. -/
@[simp]
theorem mem_moduleDualCoannihilator (T : Submodule A N) (m : M) :
    m ∈ moduleDualCoannihilator e he T ↔ ∀ n ∈ T, e n m = 0 := by
  constructor
  · intro hm n hn
    exact (Submodule.mem_dualCoannihilator _).mp hm _ ⟨n, hn, rfl⟩
  · intro hm
    exact (Submodule.mem_dualCoannihilator _).mpr fun _ ⟨n, hn, hφ⟩ ↦ hφ ▸ hm n hn

/-- Coannihilation takes a sum of left submodules to the intersection of their coannihilators. -/
@[simp]
theorem moduleDualCoannihilator_sup (T U : Submodule A N) :
    moduleDualCoannihilator e he (T ⊔ U) =
      moduleDualCoannihilator e he T ⊓ moduleDualCoannihilator e he U := by
  ext m
  -- Use the defining carriers to avoid requiring a scalar tower on the target `M`.
  change m ∈ (((T ⊔ U).restrictScalars k).map e.toLinearMap).dualCoannihilator ↔
    m ∈ ((T.restrictScalars k).map e.toLinearMap).dualCoannihilator ⊓
      ((U.restrictScalars k).map e.toLinearMap).dualCoannihilator
  rw [Submodule.restrictScalars_sup, Submodule.map_sup, Submodule.dualCoannihilator_sup_eq]

/-- Every vector is annihilated by the zero submodule of the dual. -/
@[simp]
theorem moduleDualCoannihilator_bot :
    moduleDualCoannihilator e he (⊥ : Submodule A N) = ⊤ := by
  ext m
  simp

end Coannihilator

variable [IsScalarTower k Aᵐᵒᵖ M] [IsScalarTower k A N]

/-- After forgetting the algebra action, module annihilation is ordinary annihilation
transported by the chosen dual identification. -/
theorem moduleDualAnnihilator_restrictScalars (S : Submodule Aᵐᵒᵖ M) :
    (moduleDualAnnihilator e he S).restrictScalars k =
      (S.restrictScalars k).dualAnnihilator.comap e.toLinearMap := (rfl)

/-- After forgetting the algebra action, module coannihilation is ordinary coannihilation
of the image under the chosen dual identification. -/
theorem moduleDualCoannihilator_restrictScalars (T : Submodule A N) :
    (moduleDualCoannihilator e he T).restrictScalars k =
      ((T.restrictScalars k).map e.toLinearMap).dualCoannihilator := (rfl)

/-- The annihilator of the whole module is zero. -/
@[simp]
theorem moduleDualAnnihilator_top :
    moduleDualAnnihilator e he (⊤ : Submodule Aᵐᵒᵖ M) = ⊥ := by
  apply Submodule.restrictScalars_injective k
  simp [moduleDualAnnihilator_restrictScalars, LinearEquiv.ker]

end Semiring

section Field

variable {k : Type u} {A : Type v} {M : Type w} {N : Type t}
  [Field k] [Semiring A] [Algebra k A]
  [AddCommGroup M] [Module Aᵐᵒᵖ M] [Module k M] [IsScalarTower k Aᵐᵒᵖ M]
  [AddCommGroup N] [Module A N] [Module k N] [IsScalarTower k A N]
  (e : N ≃ₗ[k] Module.Dual k M)
  (he : ∀ (a : A) (n : N) (m : M), e (a • n) m = e n (MulOpposite.op a • m))

/-- Over a field, annihilation takes an intersection to the sum of the annihilators.
No finite-dimensionality assumption is needed. -/
@[simp]
theorem moduleDualAnnihilator_inf (S T : Submodule Aᵐᵒᵖ M) :
    moduleDualAnnihilator e he (S ⊓ T) =
      moduleDualAnnihilator e he S ⊔ moduleDualAnnihilator e he T := by
  apply Submodule.restrictScalars_injective k
  simp only [moduleDualAnnihilator_restrictScalars, Submodule.restrictScalars_inf,
    Submodule.restrictScalars_sup, Subspace.dualAnnihilator_inf_eq]
  simp only [Submodule.comap_equiv_eq_map_symm, Submodule.map_sup]

/-- Coannihilation takes an intersection of finite-dimensional left submodules to the sum
of their coannihilators. The original module need not be finite-dimensional. -/
@[simp]
theorem moduleDualCoannihilator_inf (T U : Submodule A N)
    [FiniteDimensional k (T.restrictScalars k)] [FiniteDimensional k (U.restrictScalars k)] :
    moduleDualCoannihilator e he (T ⊓ U) =
      moduleDualCoannihilator e he T ⊔ moduleDualCoannihilator e he U := by
  apply Submodule.restrictScalars_injective k
  simp only [moduleDualCoannihilator_restrictScalars, Submodule.restrictScalars_inf,
    Submodule.restrictScalars_sup, Submodule.map_inf _ e.injective,
    Subspace.dualCoannihilator_inf]

/-- Double annihilation recovers a right submodule. This direction does not need finite
dimensionality. -/
@[simp]
theorem moduleDualCoannihilator_moduleDualAnnihilator (S : Submodule Aᵐᵒᵖ M) :
    moduleDualCoannihilator e he (moduleDualAnnihilator e he S) = S := by
  apply Submodule.restrictScalars_injective k
  rw [moduleDualCoannihilator_restrictScalars, moduleDualAnnihilator_restrictScalars,
    Submodule.map_comap_eq_of_surjective e.surjective,
    Subspace.dualAnnihilator_dualCoannihilator_eq]

/-- Annihilation reverses and reflects inclusion of module submodules. -/
theorem moduleDualAnnihilator_le_moduleDualAnnihilator_iff (S T : Submodule Aᵐᵒᵖ M) :
    moduleDualAnnihilator e he S ≤ moduleDualAnnihilator e he T ↔ T ≤ S := by
  rw [← Submodule.restrictScalars_le k, moduleDualAnnihilator_restrictScalars,
    moduleDualAnnihilator_restrictScalars,
    Submodule.comap_le_comap_iff_of_surjective e.surjective,
    Subspace.dualAnnihilator_le_dualAnnihilator_iff, Submodule.restrictScalars_le]

/-- Only zero is annihilated by the whole dual module. -/
@[simp]
theorem moduleDualCoannihilator_top :
    moduleDualCoannihilator e he (⊤ : Submodule A N) = ⊥ := by
  rw [← moduleDualAnnihilator_bot e he, moduleDualCoannihilator_moduleDualAnnihilator]

variable [FiniteDimensional k M]

/-- Double coannihilation recovers a left submodule of the dual of a finite-dimensional
module. -/
@[simp]
theorem moduleDualAnnihilator_moduleDualCoannihilator (T : Submodule A N) :
    moduleDualAnnihilator e he (moduleDualCoannihilator e he T) = T := by
  apply Submodule.restrictScalars_injective k
  rw [moduleDualAnnihilator_restrictScalars, moduleDualCoannihilator_restrictScalars,
    Subspace.dualCoannihilator_dualAnnihilator_eq,
    Submodule.comap_map_eq_of_injective e.injective]

/-- Annihilation reverses the submodule lattices of a finite-dimensional right module
and its left dual. -/
def moduleDualSubmoduleOrderIso : Submodule Aᵐᵒᵖ M ≃o (Submodule A N)ᵒᵈ where
  toFun S := OrderDual.toDual (moduleDualAnnihilator e he S)
  invFun T := moduleDualCoannihilator e he (OrderDual.ofDual T)
  left_inv S := moduleDualCoannihilator_moduleDualAnnihilator e he S
  right_inv T := congrArg OrderDual.toDual
    (moduleDualAnnihilator_moduleDualCoannihilator e he (OrderDual.ofDual T))
  map_rel_iff' {S T} := moduleDualAnnihilator_le_moduleDualAnnihilator_iff e he T S

/-- The annihilator order isomorphism sends a submodule to its module annihilator. -/
@[simp]
theorem moduleDualSubmoduleOrderIso_apply (S : Submodule Aᵐᵒᵖ M) :
    moduleDualSubmoduleOrderIso e he S = OrderDual.toDual (moduleDualAnnihilator e he S) :=
  (rfl)

/-- The inverse annihilator order isomorphism is module coannihilation. -/
@[simp]
theorem moduleDualSubmoduleOrderIso_symm_apply (T : Submodule A N) :
    (moduleDualSubmoduleOrderIso e he).symm (OrderDual.toDual T) =
      moduleDualCoannihilator e he T := (rfl)

/-- A right submodule is superfluous exactly when its annihilator in the left dual
is essential. -/
theorem isEssential_moduleDualAnnihilator_iff (S : Submodule Aᵐᵒᵖ M) :
    IsEssential (moduleDualAnnihilator e he S) ↔ IsSuperfluous S := by
  let E := moduleDualSubmoduleOrderIso e he
  have htop : moduleDualAnnihilator e he ⊤ = ⊥ := congrArg OrderDual.ofDual E.map_top
  rw [isEssential_iff, isSuperfluous_iff]
  constructor
  · intro h T hT
    apply E.injective
    exact congrArg OrderDual.toDual
      ((h _ ((moduleDualAnnihilator_sup e he S T).symm.trans
        ((congrArg (moduleDualAnnihilator e he) hT).trans htop))).trans htop.symm)
  · intro h T hT
    obtain ⟨U, hU⟩ := E.surjective (OrderDual.toDual T)
    have hann : moduleDualAnnihilator e he U = T := congrArg OrderDual.ofDual hU
    have hmeet : moduleDualAnnihilator e he S ⊓ moduleDualAnnihilator e he U = ⊥ := by
      rw [hann]
      exact hT
    have hsum' : moduleDualAnnihilator e he (S ⊔ U) = moduleDualAnnihilator e he ⊤ :=
      (moduleDualAnnihilator_sup e he S U).trans
        (hmeet.trans htop.symm)
    have hsum : S ⊔ U = ⊤ := E.injective (congrArg OrderDual.toDual hsum')
    rw [← hann, h U hsum, htop]

end Field

end TauCeti
