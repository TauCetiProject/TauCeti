/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.LinearAlgebra.RootSystem.Weyl.Affine.Coxeter
public import TauCeti.LinearAlgebra.RootSystem.Weyl.ExtendedAffine.Semidirect

/-!
# Length on extended affine Weyl groups

Multiplication identifies the extended affine Weyl group with `W_aff ⋊ Ω`, where `Ω` stabilizes
the fundamental alcove. Its length is the Coxeter length of the first factor. More generally
the same construction applies to every intermediate lattice between the coroot and coweight
lattices. Conjugation by `Ω` preserves the length of the affine Weyl group, since it preserves
the number of separating affine root hyperplanes. Consequently it permutes the simple
reflections.

## References

* N. Bourbaki, *Lie Groups and Lie Algebras, Chapters 4–6*, Ch. VI, §2.3.
* G. Pappas and M. Rapoport, *Twisted loop groups and their affine flag varieties*, §8.
-/

public section

open Set Function

namespace RootPairing

section SeparatingRoots

variable {ι R M N : Type*} [CommRing R] [AddCommGroup M] [Module R M] [AddCommGroup N]
  [Module R N] (P : RootPairing ι R M N) [PartialOrder R] [IsOrderedAddMonoid R]

/-- The extended affine Weyl group preserves the number of affine roots separating two points.
This counts indexed affine roots and does not require the root pairing to be reduced. -/
theorem ncard_separatingAffineRoots_apply_of_mem_extendedAffineWeylGroup
    {f : N ≃ᵃ[R] N} (hf : f ∈ P.extendedAffineWeylGroup) (x y : N) :
    (P.separatingAffineRoots (f x) (f y)).ncard = (P.separatingAffineRoots x y).ncard := by
  classical
  obtain ⟨π, hπ, hπc⟩ :=
    P.exists_root'_apply_eq_and_apply_coroot_eq_of_mem_closure_range_coreflection
      (P.mem_extendedAffineWeylGroup_iff.mp hf).1
  have hπinj : Injective π := fun i j hij ↦ P.coroot.injective <| by
    rw [← hπc i, ← hπc j, hij]
  have hπsurj : Surjective π := by
    obtain ⟨ρ, _, hρc⟩ :=
      P.exists_root'_apply_eq_and_apply_coroot_eq_of_mem_closure_range_coreflection
        (inv_mem (P.mem_extendedAffineWeylGroup_iff.mp hf).1)
    intro j
    refine ⟨ρ j, P.coroot.injective (f.linear.injective ?_)⟩
    rw [hπc]
    simpa using congrArg f.linear (hρc j)
  have hm := P.mem_coweightLattice.mp (P.mem_extendedAffineWeylGroup_iff.mp hf).2
  choose m hm using hm
  have hroot (j : ι) (z : N) : P.root' j (f z) = P.root' (π j) z + (m j : R) := by
    rw [AffineEquiv.apply_eq_linear_add f z, map_add, hπ, hm]
  have hmem (j : ι) (k : ℤ) :
      (j, k) ∈ P.separatingAffineRoots (f x) (f y) ↔
        (π j, k - m j) ∈ P.separatingAffineRoots x y := by
    simp only [mem_separatingAffineRoots, hroot, Int.cast_sub, sub_lt_iff_lt_add,
      lt_sub_iff_add_lt]
  refine Set.ncard_congr (fun p _ ↦ (π p.1, p.2 - m p.1))
    (fun p hp ↦ (hmem p.1 p.2).mp hp) ?_ ?_
  · rintro ⟨i, k⟩ ⟨j, l⟩ _ _ h
    have hij : i = j := hπinj (congrArg Prod.fst h)
    subst j
    exact Prod.ext rfl (by simpa using congrArg Prod.snd h)
  · rintro ⟨j, k⟩ hk
    obtain ⟨i, rfl⟩ := hπsurj j
    exact ⟨(i, k + m i), (hmem i _).mpr (by simpa using hk), by simp⟩

end SeparatingRoots

namespace Base

variable {ι R M N : Type*} [Field R] [LinearOrder R] [IsStrictOrderedRing R]
  [AddCommGroup M] [Module R M] [AddCommGroup N] [Module R N]
  {P : RootPairing ι R M N} [Finite ι] [Nonempty ι]
  [P.IsCrystallographic] [P.IsReduced] [P.IsIrreducible] [DecidableEq ι] (b : P.Base)

/-- Conjugation by an alcove stabilizer preserves affine Coxeter length. -/
theorem affineWeylCoxeterSystem_length_conj
    (ω : P.fundamentalAlcoveStabilizer b) (w : P.affineWeylGroup) :
    b.affineWeylCoxeterSystem.length
      (P.affineWeylGroup.normalizerMonoidHom
        (Subgroup.inclusion (fundamentalAlcoveStabilizer_le_normalizer_affineWeylGroup b) ω) w) =
      b.affineWeylCoxeterSystem.length w := by
  obtain ⟨x, hx⟩ := fundamentalAlcove_nonempty b
  have hω := (P.mem_fundamentalAlcoveStabilizer b).mp ω.property
  have hωx : ω.val x ∈ fundamentalAlcove P b := hω.2 ▸ mem_image_of_mem _ hx
  rw [b.affineWeylCoxeterSystem_length hωx, b.affineWeylCoxeterSystem_length hx]
  simpa [AffineEquiv.inv_def] using
    P.ncard_separatingAffineRoots_apply_of_mem_extendedAffineWeylGroup hω.1
      x ((w : N ≃ᵃ[R] N) x)

/-- Conjugation by an alcove stabilizer permutes the affine simple reflections. -/
theorem image_conj_range_affineWeylCoxeterSystem_simple
    (ω : P.fundamentalAlcoveStabilizer b) :
    let e := P.affineWeylGroup.normalizerMonoidHom
      (Subgroup.inclusion (fundamentalAlcoveStabilizer_le_normalizer_affineWeylGroup b) ω)
    e '' range b.affineWeylCoxeterSystem.simple = range b.affineWeylCoxeterSystem.simple := by
  intro e
  have hlen := b.affineWeylCoxeterSystem_length_conj ω
  ext w
  constructor
  · rintro ⟨_, ⟨k, rfl⟩, rfl⟩
    obtain ⟨j, hj⟩ := b.affineWeylCoxeterSystem.length_eq_one_iff.mp
      ((hlen _).trans (b.affineWeylCoxeterSystem.length_simple k))
    exact ⟨j, hj.symm⟩
  · rintro ⟨k, rfl⟩
    have h : b.affineWeylCoxeterSystem.length
        (e.symm (b.affineWeylCoxeterSystem.simple k)) = 1 := by
      rw [← hlen, e.apply_symm_apply, b.affineWeylCoxeterSystem.length_simple]
    obtain ⟨j, hj⟩ := b.affineWeylCoxeterSystem.length_eq_one_iff.mp h
    exact ⟨_, ⟨j, hj.symm⟩, e.apply_symm_apply _⟩

variable [Archimedean R]

/-- Length on the extended affine Weyl group: the Coxeter length of the affine factor in
`W_ext = W_aff ⋊ Ω`. -/
noncomputable def extendedAffineLength (f : P.extendedAffineWeylGroup) : ℕ :=
  b.affineWeylCoxeterSystem.length ((P.extendedAffineWeylGroupMulEquiv b).symm f).left

/-- The affine factor computes extended affine length. -/
theorem extendedAffineLength_def (f : P.extendedAffineWeylGroup) :
    b.extendedAffineLength f =
      b.affineWeylCoxeterSystem.length ((P.extendedAffineWeylGroupMulEquiv b).symm f).left :=
  (rfl)

/-- The length of `wω` is the Coxeter length of `w`. -/
@[simp]
theorem extendedAffineLength_mulEquiv
    (x : P.affineWeylGroup ⋊[(P.affineWeylGroup.normalizerMonoidHom).comp
      (Subgroup.inclusion (fundamentalAlcoveStabilizer_le_normalizer_affineWeylGroup b))]
      P.fundamentalAlcoveStabilizer b) :
    b.extendedAffineLength (P.extendedAffineWeylGroupMulEquiv b x) =
      b.affineWeylCoxeterSystem.length x.left := by
  simp [extendedAffineLength]

/-- Length vanishes exactly on the stabilizer of the fundamental alcove. -/
@[simp]
theorem extendedAffineLength_eq_zero_iff (f : P.extendedAffineWeylGroup) :
    b.extendedAffineLength f = 0 ↔ (f : N ≃ᵃ[R] N) ∈ P.fundamentalAlcoveStabilizer b := by
  obtain ⟨x, rfl⟩ := (P.extendedAffineWeylGroupMulEquiv b).surjective f
  rw [extendedAffineLength_mulEquiv, b.affineWeylCoxeterSystem.length_eq_zero_iff]
  constructor
  · intro h
    simpa only [coe_extendedAffineWeylGroupMulEquiv_apply, h, OneMemClass.coe_one, one_mul]
      using x.right.property
  · intro h
    have hx : (x.left : N ≃ᵃ[R] N) ∈ P.fundamentalAlcoveStabilizer b := by
      have hm := mul_mem h (inv_mem x.right.property)
      simpa using hm
    have hm : (x.left : N ≃ᵃ[R] N) ∈
        P.affineWeylGroup ⊓ P.fundamentalAlcoveStabilizer b := ⟨x.left.property, hx⟩
    rw [affineWeylGroup_inf_fundamentalAlcoveStabilizer, Subgroup.mem_bot] at hm
    exact Subtype.ext hm

/-- The length of an extended affine Weyl element is the number of affine root hyperplanes
separating the fundamental alcove from its image. -/
theorem extendedAffineLength_eq_ncard (f : P.extendedAffineWeylGroup) {x : N}
    (hx : x ∈ fundamentalAlcove P b) :
    b.extendedAffineLength f =
      (P.separatingAffineRoots x ((f : N ≃ᵃ[R] N) x)).ncard := by
  obtain ⟨g, rfl⟩ := (P.extendedAffineWeylGroupMulEquiv b).surjective f
  have hω := (P.mem_fundamentalAlcoveStabilizer b).mp g.right.property
  have hωx : g.right.val x ∈ fundamentalAlcove P b := hω.2 ▸ mem_image_of_mem _ hx
  rw [extendedAffineLength_mulEquiv, b.affineWeylCoxeterSystem_length hωx]
  congr 1
  ext p
  simp only [mem_separatingAffineRoots, coe_extendedAffineWeylGroupMulEquiv_apply,
    AffineEquiv.coe_mul, comp_apply]
  exact and_congr_left fun _ ↦ ((mem_fundamentalAlcove_iff_of_mem hx).mp hωx p.1 p.2).1

/-- The identity has length zero. -/
@[simp]
theorem extendedAffineLength_one : b.extendedAffineLength 1 = 0 :=
  (b.extendedAffineLength_eq_zero_iff 1).mpr (one_mem _)

/-- An alcove stabilizer has length zero. -/
@[simp]
theorem extendedAffineLength_stabilizer (ω : P.fundamentalAlcoveStabilizer b) :
    b.extendedAffineLength (Subgroup.inclusion
      (P.fundamentalAlcoveStabilizer_le_extendedAffineWeylGroup b) ω) = 0 :=
  (b.extendedAffineLength_eq_zero_iff _).mpr ω.property

/-- Inversion preserves extended affine length. -/
@[simp]
theorem extendedAffineLength_inv (f : P.extendedAffineWeylGroup) :
    b.extendedAffineLength f⁻¹ = b.extendedAffineLength f := by
  rw [extendedAffineLength, map_inv, SemidirectProduct.inv_left]
  exact (b.affineWeylCoxeterSystem_length_conj
    ((P.extendedAffineWeylGroupMulEquiv b).symm f).right⁻¹
    ((P.extendedAffineWeylGroupMulEquiv b).symm f).left⁻¹).trans
      (b.affineWeylCoxeterSystem.length_inv _)

/-- Right multiplication by an alcove stabilizer preserves extended affine length. -/
@[simp]
theorem extendedAffineLength_mul_stabilizer (f : P.extendedAffineWeylGroup)
    (ω : P.fundamentalAlcoveStabilizer b) :
    b.extendedAffineLength (f * Subgroup.inclusion
      (P.fundamentalAlcoveStabilizer_le_extendedAffineWeylGroup b) ω) =
      b.extendedAffineLength f := by
  obtain ⟨x, rfl⟩ := (P.extendedAffineWeylGroupMulEquiv b).surjective f
  have hω : Subgroup.inclusion (P.fundamentalAlcoveStabilizer_le_extendedAffineWeylGroup b) ω =
      P.extendedAffineWeylGroupMulEquiv b (.inr ω) := by
    apply Subtype.ext
    simp
  rw [hω, ← map_mul, extendedAffineLength_mulEquiv, extendedAffineLength_mulEquiv]
  simp

/-- Left multiplication by an alcove stabilizer preserves extended affine length. -/
@[simp]
theorem extendedAffineLength_stabilizer_mul (f : P.extendedAffineWeylGroup)
    (ω : P.fundamentalAlcoveStabilizer b) :
    b.extendedAffineLength (Subgroup.inclusion
      (P.fundamentalAlcoveStabilizer_le_extendedAffineWeylGroup b) ω * f) =
      b.extendedAffineLength f := by
  rw [← extendedAffineLength_inv, mul_inv_rev, ← map_inv,
    extendedAffineLength_mul_stabilizer, extendedAffineLength_inv]

/-- Conjugation by a length-zero element preserves extended affine length. -/
theorem extendedAffineLength_stabilizer_conj (f : P.extendedAffineWeylGroup)
    (ω : P.fundamentalAlcoveStabilizer b) :
    b.extendedAffineLength (Subgroup.inclusion
        (P.fundamentalAlcoveStabilizer_le_extendedAffineWeylGroup b) ω * f *
      (Subgroup.inclusion (P.fundamentalAlcoveStabilizer_le_extendedAffineWeylGroup b) ω)⁻¹) =
      b.extendedAffineLength f := by
  rw [← map_inv, extendedAffineLength_mul_stabilizer, extendedAffineLength_stabilizer_mul]

section Lattice

variable (Y : Submodule ℤ N) (hQ : P.corootSpan ℤ ≤ Y) (hP : Y ≤ P.coweightLattice)

/-- Length on the affine Weyl group of an intermediate lattice, obtained by restriction from
the extended affine Weyl group. -/
noncomputable def latticeAffineLength (f : P.latticeAffineWeylGroup Y hQ hP) : ℕ :=
  b.extendedAffineLength
    (Subgroup.inclusion (P.latticeAffineWeylGroup_le_extendedAffineWeylGroup hQ hP) f)

/-- Lattice affine length agrees with extended affine length under the canonical inclusion. -/
theorem latticeAffineLength_eq_extendedAffineLength
    (f : P.latticeAffineWeylGroup Y hQ hP) :
    b.latticeAffineLength Y hQ hP f = b.extendedAffineLength
      (Subgroup.inclusion (P.latticeAffineWeylGroup_le_extendedAffineWeylGroup hQ hP) f) :=
  (rfl)

/-- The semidirect normal form `wω` has length equal to the Coxeter length of `w`. -/
@[simp]
theorem latticeAffineLength_mulEquiv
    (g : P.affineWeylGroup ⋊[(P.affineWeylGroup.normalizerMonoidHom).comp
      (Subgroup.inclusion
        (latticeFundamentalAlcoveStabilizer_le_normalizer_affineWeylGroup b hQ hP))]
      P.latticeFundamentalAlcoveStabilizer b Y hQ hP) :
    b.latticeAffineLength Y hQ hP (P.latticeAffineWeylGroupMulEquiv b Y hQ hP g) =
      b.affineWeylCoxeterSystem.length g.left := by
  rw [latticeAffineLength_eq_extendedAffineLength]
  rw [inclusion_latticeAffineWeylGroupMulEquiv, extendedAffineLength_mulEquiv]

/-- The length-zero subgroup for an intermediate lattice is its fundamental alcove stabilizer. -/
@[simp]
theorem latticeAffineLength_eq_zero_iff (f : P.latticeAffineWeylGroup Y hQ hP) :
    b.latticeAffineLength Y hQ hP f = 0 ↔
      (f : N ≃ᵃ[R] N) ∈ P.latticeFundamentalAlcoveStabilizer b Y hQ hP := by
  rw [latticeAffineLength_eq_extendedAffineLength, extendedAffineLength_eq_zero_iff,
    mem_latticeFundamentalAlcoveStabilizer]
  exact (and_iff_left ((P.mem_latticeAffineWeylGroup_iff hQ hP).mp f.property).2).symm

/-- Lattice affine length also counts the affine hyperplanes separating the alcoves. -/
theorem latticeAffineLength_eq_ncard (f : P.latticeAffineWeylGroup Y hQ hP) {x : N}
    (hx : x ∈ fundamentalAlcove P b) :
    b.latticeAffineLength Y hQ hP f =
      (P.separatingAffineRoots x ((f : N ≃ᵃ[R] N) x)).ncard :=
  b.extendedAffineLength_eq_ncard _ hx

/-- Inversion preserves lattice affine length. -/
@[simp]
theorem latticeAffineLength_inv (f : P.latticeAffineWeylGroup Y hQ hP) :
    b.latticeAffineLength Y hQ hP f⁻¹ = b.latticeAffineLength Y hQ hP f := by
  simp [latticeAffineLength_eq_extendedAffineLength]

/-- The identity has lattice affine length zero. -/
@[simp]
theorem latticeAffineLength_one : b.latticeAffineLength Y hQ hP 1 = 0 := by
  simp [latticeAffineLength_eq_extendedAffineLength]

/-- An element of the lattice alcove stabilizer has length zero. -/
@[simp]
theorem latticeAffineLength_stabilizer
    (ω : P.latticeFundamentalAlcoveStabilizer b Y hQ hP) :
    b.latticeAffineLength Y hQ hP (Subgroup.inclusion
      (latticeFundamentalAlcoveStabilizer_le_latticeAffineWeylGroup b hQ hP) ω) = 0 :=
  (b.latticeAffineLength_eq_zero_iff Y hQ hP _).mpr ω.property

/-- Conjugation by a lattice alcove stabilizer preserves lattice affine length. -/
theorem latticeAffineLength_stabilizer_conj (f : P.latticeAffineWeylGroup Y hQ hP)
    (ω : P.latticeFundamentalAlcoveStabilizer b Y hQ hP) :
    let i := Subgroup.inclusion
      (latticeFundamentalAlcoveStabilizer_le_latticeAffineWeylGroup b hQ hP)
    b.latticeAffineLength Y hQ hP (i ω * f * (i ω)⁻¹) = b.latticeAffineLength Y hQ hP f := by
  intro i
  have hω : Subgroup.inclusion
      (P.latticeAffineWeylGroup_le_extendedAffineWeylGroup hQ hP) (i ω) =
      Subgroup.inclusion (P.fundamentalAlcoveStabilizer_le_extendedAffineWeylGroup b)
        (Subgroup.inclusion
          (latticeFundamentalAlcoveStabilizer_le_fundamentalAlcoveStabilizer b hQ hP) ω) := by
    apply Subtype.ext
    simp [i]
  simp only [latticeAffineLength_eq_extendedAffineLength, map_mul, map_inv, hω,
    extendedAffineLength_stabilizer_conj]

end Lattice

end Base

end RootPairing
