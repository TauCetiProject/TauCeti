/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.GroupTheory.GroupAlgGeom.Basic

/-!
# Separation and discrimination of groups with coefficients

A group under `G` is separated by another when each nonidentity element survives under some
homomorphism fixing `G`. Discrimination asks for one homomorphism to preserve every element of
any given finite family simultaneously. The latter is the relative version of full residuality
used to recognize irreducible coordinate groups and, with trivial coefficients, limit groups.

The coefficient maps need not be injective: the same definitions apply to the coefficient maps
of quotients of free `G`-groups, even before the quotient is known to be a `G`-group.

## References

* G. Baumslag, A. Myasnikov, V. Remeslennikov, *Algebraic geometry over groups I. Algebraic sets
  and ideal theory*, J. Algebra 219 (1999), §1.
* O. Kharlampovich, A. Myasnikov, *Implicit function theorem over free groups*, J. Algebra 290
  (2005), §2.5.
-/

public section

namespace TauCeti.GroupAlgGeom

variable {G K H L : Type*} [Group G] [Group K] [Group H] [Group L]

/-- `K` is separated by `H` over `G` when every nonidentity element of `K` survives in some
homomorphism to `H` fixing the coefficients. -/
def IsSeparatedBy (ιK : G →* K) (ιH : G →* H) : Prop :=
  ∀ k : K, k ≠ 1 → ∃ φ : GHom ιK ιH, φ k ≠ 1

/-- `K` is discriminated by `H` over `G` when any finite family of nonidentity elements of `K`
survives simultaneously under one homomorphism to `H` fixing the coefficients. -/
def IsDiscriminatedBy (ιK : G →* K) (ιH : G →* H) : Prop :=
  ∀ s : Finset K, (∀ k ∈ s, k ≠ 1) →
    ∃ φ : GHom ιK ιH, ∀ k ∈ s, φ k ≠ 1

/-- Characterization of separation by coefficient-preserving homomorphisms. -/
theorem isSeparatedBy_def (ιK : G →* K) (ιH : G →* H) :
    IsSeparatedBy ιK ιH ↔ ∀ k : K, k ≠ 1 → ∃ φ : GHom ιK ιH, φ k ≠ 1 :=
  Iff.rfl

/-- Characterization of discrimination by coefficient-preserving homomorphisms. -/
theorem isDiscriminatedBy_def (ιK : G →* K) (ιH : G →* H) :
    IsDiscriminatedBy ιK ιH ↔
      ∀ s : Finset K, (∀ k ∈ s, k ≠ 1) →
        ∃ φ : GHom ιK ιH, ∀ k ∈ s, φ k ≠ 1 :=
  Iff.rfl

namespace IsDiscriminatedBy

/-- Discrimination implies separation by testing a singleton. -/
theorem isSeparatedBy {ιK : G →* K} {ιH : G →* H}
    (h : IsDiscriminatedBy ιK ιH) : IsSeparatedBy ιK ιH := by
  classical
  intro k hk
  obtain ⟨φ, hφ⟩ := h {k} (by simpa using hk)
  exact ⟨φ, hφ k (by simp)⟩

/-- The source of an injective coefficient-preserving map into a discriminated group is
discriminated by the same target. -/
theorem of_injective {ιK : G →* K} {ιL : G →* L} {ιH : G →* H}
    (h : IsDiscriminatedBy ιL ιH) (f : GHom ιK ιL) (hf : Function.Injective f) :
    IsDiscriminatedBy ιK ιH := by
  classical
  intro s hs
  obtain ⟨φ, hφ⟩ := h (s.image f) (by
    simpa only [Finset.forall_mem_image, map_ne_one_iff f hf] using hs)
  refine ⟨φ.comp f, ?_⟩
  intro k hk
  simpa [GHom.coe_comp] using hφ (f k) (Finset.mem_image.mpr ⟨k, hk, rfl⟩)

/-- Every group with a coefficient map discriminates itself through the identity. -/
theorem self (ιK : G →* K) : IsDiscriminatedBy ιK ιK := by
  intro s hs
  exact ⟨GHom.id ιK, by simpa using hs⟩

end IsDiscriminatedBy

namespace IsSeparatedBy

/-- The source of an injective coefficient-preserving map into a separated group is separated
by the same target. -/
theorem of_injective {ιK : G →* K} {ιL : G →* L} {ιH : G →* H}
    (h : IsSeparatedBy ιL ιH) (f : GHom ιK ιL) (hf : Function.Injective f) :
    IsSeparatedBy ιK ιH := by
  intro k hk
  obtain ⟨φ, hφ⟩ := h (f k) ((map_ne_one_iff f hf).2 hk)
  exact ⟨φ.comp f, by simpa [GHom.coe_comp] using hφ⟩

end IsSeparatedBy

/-- Separation by `H` is equivalent to triviality of the intersection of kernels of all
coefficient-preserving homomorphisms to `H`. -/
theorem isSeparatedBy_iff_iInf_ker (ιK : G →* K) (ιH : G →* H) :
    IsSeparatedBy ιK ιH ↔
      (⨅ φ : GHom ιK ιH, (φ : K →* H).ker) = ⊥ := by
  simp only [IsSeparatedBy, Subgroup.eq_bot_iff_forall, Subgroup.mem_iInf,
    MonoidHom.mem_ker]
  exact ⟨fun h k hk => by
      by_contra hne
      obtain ⟨φ, hφ⟩ := h k hne
      exact hφ (hk φ),
    fun h k hk => by
      by_contra hall
      apply hk
      apply h k
      intro φ
      by_contra hne
      exact hall ⟨φ, hne⟩⟩

end TauCeti.GroupAlgGeom
