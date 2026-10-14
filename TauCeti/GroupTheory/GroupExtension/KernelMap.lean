/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.GroupTheory.GroupExtension.Basic

/-!
# Restricting homomorphisms of extensions to their kernels

A homomorphism between group extensions over the identity of the quotient induces a unique
homomorphism between their kernel terms. This restriction intertwines the conjugation actions,
so it can be used as a coefficient map when comparing extension classes.
-/

public section

namespace GroupExtension

variable {G M N E E' : Type*} [Group G] [Group M] [Group N] [Group E] [Group E']
  (S : GroupExtension M E G) (T : GroupExtension N E' G) (φ : E →* E')
  (hright : T.rightHom.comp φ = S.rightHom)

/-- The restriction of a homomorphism of extensions over the identity of the quotient to their
kernel terms. -/
noncomputable def kernelMap : M →* N :=
  (MonoidHom.ofInjective T.inl_injective).symm.toMonoidHom.comp
    ((φ.comp S.inl).codRestrict T.inl.range fun m ↦ by
      rw [T.range_inl_eq_ker_rightHom, MonoidHom.mem_ker, MonoidHom.comp_apply,
        ← MonoidHom.comp_apply T.rightHom φ, hright]
      exact S.rightHom_inl m)

/-- Including the kernel restriction into the target recovers the original homomorphism on
included kernel elements. -/
@[simp]
theorem inl_kernelMap (m : M) : T.inl (S.kernelMap T φ hright m) = φ (S.inl m) :=
  MonoidHom.apply_ofInjective_symm T.inl_injective _

/-- The commuting inclusion square uniquely determines the restriction to the kernels. -/
theorem kernelMap_unique (f : M →* N) (hinl : T.inl.comp f = φ.comp S.inl) :
    f = S.kernelMap T φ hright := by
  ext m
  apply T.inl_injective
  simpa using DFunLike.congr_fun hinl m

/-- Restriction to the kernels intertwines conjugation by corresponding elements of the total
groups. -/
@[simp]
theorem kernelMap_conjAct (e : E) (m : M) :
    S.kernelMap T φ hright (S.conjAct e m) =
      T.conjAct (φ e) (S.kernelMap T φ hright m) := by
  apply T.inl_injective
  simp [inl_conjAct_comm]

end GroupExtension
