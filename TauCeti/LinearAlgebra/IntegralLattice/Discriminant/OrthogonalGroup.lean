/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.LinearAlgebra.FiniteBilinearModule.OrthogonalGroup
public import TauCeti.LinearAlgebra.IntegralLattice.Discriminant.Quadratic
public import TauCeti.LinearAlgebra.IntegralLattice.Isometry.Group
public import TauCeti.LinearAlgebra.IntegralLattice.Unimodular

/-!
# The action of the isometry group on the discriminant form

A self-isometry `g` of an integral lattice `L` maps the dual lattice `Lᵛ` onto itself, so it acts
on the discriminant group `A_L = Lᵛ / L`. This action is a group homomorphism
`O(L) → Aut(A_L)`, and when `L` is even and nondegenerate it takes values in the orthogonal group
`O(q_L)` of the discriminant quadratic module. Nikulin's surjectivity theorem for
`O(L) → O(q_L)` and his description of primitive embeddings through isometries of discriminant
forms are statements about this homomorphism.

Its kernel, the *discriminant kernel* `Õ(L)`, consists of the self-isometries acting trivially on
`A_L`, that is, moving every dual vector by a lattice vector. For nondegenerate `L` it has finite
index in `O(L)`, since `A_L` is finite. It contains the principal congruence subgroup of every
level `d` with `d • A_L = 0`; it contains `-1` exactly when `A_L` is `2`-elementary; it is all of
`O(L)` when `L` is unimodular; and conjugation by an isometry `L ≅ M` carries `Õ(L)` onto `Õ(M)`.

## Main definitions

* `TauCeti.IntegralLattice.Isometry.discriminantGroupHom`: the action `O(L) →* Aut(A_L)`.
* `TauCeti.IntegralLattice.Isometry.discriminantKernel`: its kernel `Õ(L)`.
* `TauCeti.IntegralLattice.Isometry.discriminantOrthogonalHom`: for even nondegenerate `L`, the
  homomorphism `O(L) →* O(q_L)`.

## Main results

* `TauCeti.IntegralLattice.Isometry.mem_discriminantKernel_iff`: `g ∈ Õ(L)` exactly when
  `g x - x ∈ L` for every `x ∈ Lᵛ`.
* `TauCeti.IntegralLattice.Isometry.instFiniteIndexDiscriminantKernel`: `Õ(L)` has finite index for
  nondegenerate `L`.
* `TauCeti.IntegralLattice.Isometry.congruenceSubgroup_le_discriminantKernel`: the congruence
  subgroup of level `d` lies in `Õ(L)` when `d` kills `A_L`.
* `TauCeti.IntegralLattice.Isometry.neg_mem_discriminantKernel_iff`: `-1 ∈ Õ(L)` exactly when
  `2 • A_L = 0`.
* `TauCeti.IntegralLattice.IsUnimodular.discriminantKernel_eq_top`: `Õ(L) = O(L)` for unimodular
  `L`.
* `TauCeti.IntegralLattice.Isometry.map_conjMulEquiv_discriminantKernel`: conjugation by an
  isometry `L ≅ M` maps `Õ(L)` onto `Õ(M)`.
* `TauCeti.IntegralLattice.Isometry.ker_discriminantOrthogonalHom`: the kernel of
  `O(L) →* O(q_L)` is `Õ(L)`.

## References

* V. V. Nikulin, *Integral symmetric bilinear forms and some of their applications*, §1.14 and
  §1.15.
* W. Ebeling, *Lattices and Codes*, Chapter 1.
-/

public section

namespace TauCeti

namespace IntegralLattice

namespace Isometry

variable {V : Type*} [AddCommGroup V] [Module ℚ V] {L : IntegralLattice V}

/-! ### The action on the discriminant group -/

/-- The action of the isometry group `O(L)` on the discriminant group `A_L = Lᵛ / L`, as a group
homomorphism into the automorphism group of `A_L`. -/
def discriminantGroupHom (L : IntegralLattice V) :
    Isometry L L →* (L.DiscriminantGroup ≃ₗ[ℤ] L.DiscriminantGroup) where
  toFun g := g.discriminantGroupEquiv
  map_one' := discriminantGroupEquiv_refl L
  map_mul' g h := by rw [mul_def, discriminantGroupEquiv_trans, LinearEquiv.mul_eq_trans]

@[simp]
theorem discriminantGroupHom_apply (g : Isometry L L) :
    discriminantGroupHom L g = g.discriminantGroupEquiv :=
  (rfl)

/-- A self-isometry acts on the class of a dual vector through its image. -/
theorem discriminantGroupHom_apply_mk (g : Isometry L L) (x : L.dualCarrier) :
    discriminantGroupHom L g (Submodule.Quotient.mk x) =
      Submodule.Quotient.mk (g.dualCarrierEquiv x) := by
  simp

/-- Negation acts on the discriminant group as negation. -/
@[simp]
theorem discriminantGroupEquiv_neg (L : IntegralLattice V) :
    (neg L).discriminantGroupEquiv = LinearEquiv.neg ℤ := by
  ext a
  induction a using Submodule.Quotient.induction_on with
  | _ x =>
    rw [discriminantGroupEquiv_mk, LinearEquiv.neg_apply, ← Submodule.Quotient.mk_neg]
    congr 1
    ext
    simp

/-! ### The discriminant kernel -/

/-- The discriminant kernel `Õ(L)`: the self-isometries of `L` acting trivially on the
discriminant group `A_L`. -/
def discriminantKernel (L : IntegralLattice V) : Subgroup (Isometry L L) :=
  (discriminantGroupHom L).ker

/-- The discriminant kernel is the kernel of the action `O(L) →* Aut(A_L)`. -/
@[simp]
theorem ker_discriminantGroupHom (L : IntegralLattice V) :
    (discriminantGroupHom L).ker = discriminantKernel L :=
  (rfl)

instance (L : IntegralLattice V) : (discriminantKernel L).Normal :=
  MonoidHom.normal_ker _

/-- A self-isometry lies in the discriminant kernel exactly when it moves every vector of the dual
lattice by a vector of the lattice. -/
theorem mem_discriminantKernel_iff {g : Isometry L L} :
    g ∈ discriminantKernel L ↔ ∀ x ∈ L.dualCarrier, g x - x ∈ L.carrier := by
  rw [discriminantKernel, MonoidHom.mem_ker]
  refine ⟨fun hg x hx ↦ ?_, fun hg ↦ LinearEquiv.ext fun a ↦ ?_⟩
  · have h := LinearEquiv.congr_fun hg (Submodule.Quotient.mk ⟨x, hx⟩)
    rw [discriminantGroupHom_apply_mk, LinearEquiv.coe_one, id_eq,
      L.discriminantGroup_mk_eq_iff] at h
    simpa using h
  · induction a using Submodule.Quotient.induction_on with
    | _ x =>
      rw [discriminantGroupHom_apply_mk, LinearEquiv.coe_one, id_eq,
        L.discriminantGroup_mk_eq_iff]
      simpa using hg x x.property

/-- For a nondegenerate lattice the discriminant kernel has finite index in `O(L)`, because the
discriminant group is finite. -/
instance instFiniteIndexDiscriminantKernel (L : IntegralLattice V) [L.IsNondegenerate] :
    (discriminantKernel L).FiniteIndex := by
  have : Finite (L.DiscriminantGroup ≃ₗ[ℤ] L.DiscriminantGroup) := FunLike.finite _
  rw [discriminantKernel]
  infer_instance

/-- The principal congruence subgroup of any level `d` that kills the discriminant group lies in the
discriminant kernel: if `g x ≡ x` modulo `d L` for `x ∈ L` and `d Lᵛ ⊆ L`, then `g x ≡ x` modulo
`L` for `x ∈ Lᵛ`. -/
theorem congruenceSubgroup_le_discriminantKernel {d : ℤ}
    (hd : ∀ a : L.DiscriminantGroup, d • a = 0) :
    congruenceSubgroup L d ≤ discriminantKernel L := by
  intro g hg
  rcases eq_or_ne d 0 with rfl | hd0
  · -- At level zero the congruence subgroup is trivial.
    have h1 : g = 1 := carrierEquivHom_injective L <| LinearEquiv.ext fun x ↦ by
      obtain ⟨y, hy⟩ := mem_congruenceSubgroup_iff.mp hg x
      rw [zero_smul, sub_eq_zero] at hy
      rw [carrierEquivHom_apply, hy, map_one, LinearEquiv.coe_one, id_eq]
    rw [h1]
    exact one_mem _
  rw [mem_discriminantKernel_iff]
  intro x hx
  have hdx : d • x ∈ L.carrier := by
    have h := hd (Submodule.Quotient.mk ⟨x, hx⟩)
    rw [← Submodule.Quotient.mk_smul, L.discriminantGroup_mk_eq_zero_iff] at h
    simpa using h
  obtain ⟨y, hy⟩ := mem_congruenceSubgroup_iff.mp hg ⟨d • x, hdx⟩
  have hy' : d • (g x - x) = d • (y : V) := by
    have := congrArg (fun z : L ↦ (z : V)) hy
    simpa [coe_carrierEquiv_apply, smul_sub] using this
  have hinj : g x - x = (y : V) := by
    rw [← Int.cast_smul_eq_zsmul ℚ, ← Int.cast_smul_eq_zsmul ℚ d (y : V)] at hy'
    exact smul_right_injective V (Int.cast_ne_zero.mpr hd0) hy'
  rw [hinj]
  exact y.property

/-- Negation lies in the discriminant kernel exactly when the discriminant group is
`2`-elementary, that is, killed by `2`. -/
theorem neg_mem_discriminantKernel_iff :
    neg L ∈ discriminantKernel L ↔ ∀ a : L.DiscriminantGroup, (2 : ℤ) • a = 0 := by
  rw [discriminantKernel, MonoidHom.mem_ker, discriminantGroupHom_apply, discriminantGroupEquiv_neg]
  refine ⟨fun h a ↦ ?_, fun h ↦ LinearEquiv.ext fun a ↦ ?_⟩
  · have ha := LinearEquiv.congr_fun h a
    rw [LinearEquiv.neg_apply, LinearEquiv.coe_one, id_eq, neg_eq_iff_add_eq_zero] at ha
    rw [two_zsmul, ha]
  · rw [LinearEquiv.neg_apply, LinearEquiv.coe_one, id_eq, neg_eq_iff_add_eq_zero, ← two_zsmul]
    exact h a

/-! ### Conjugation -/

variable {W : Type*} [AddCommGroup W] [Module ℚ W] {M : IntegralLattice W}

/-- Conjugation by an isometry `e : L ≅ M` corresponds, on discriminant groups, to conjugation by
the induced equivalence `A_L ≃ A_M`. -/
theorem discriminantGroupHom_conjMulEquiv (e : Isometry L M) (g : Isometry L L) :
    discriminantGroupHom M (e.conjMulEquiv g) =
      (e.discriminantGroupEquiv.symm.trans (discriminantGroupHom L g)).trans
        e.discriminantGroupEquiv := by
  have h : e.conjMulEquiv g = (e.symm.trans g).trans e :=
    Isometry.ext fun y ↦ by rw [conjMulEquiv_apply, trans_apply, trans_apply]
  rw [discriminantGroupHom_apply, discriminantGroupHom_apply, h, discriminantGroupEquiv_trans,
    discriminantGroupEquiv_trans, discriminantGroupEquiv_symm]

/-- Conjugation by an isometry preserves membership in the discriminant kernel. -/
@[simp]
theorem conjMulEquiv_mem_discriminantKernel_iff (e : Isometry L M) {g : Isometry L L} :
    e.conjMulEquiv g ∈ discriminantKernel M ↔ g ∈ discriminantKernel L := by
  simp only [discriminantKernel, MonoidHom.mem_ker, discriminantGroupHom_conjMulEquiv]
  constructor
  · intro h
    ext a
    simpa using congrArg e.discriminantGroupEquiv.symm
      (LinearEquiv.congr_fun h (e.discriminantGroupEquiv a))
  · intro h
    ext b
    simp [h]

/-- Conjugation by an isometry `L ≅ M` maps the discriminant kernel of `L` onto that of `M`. -/
theorem map_conjMulEquiv_discriminantKernel (e : Isometry L M) :
    (discriminantKernel L).map e.conjMulEquiv.toMonoidHom = discriminantKernel M := by
  ext g
  rw [Subgroup.mem_map_equiv, ← conjMulEquiv_mem_discriminantKernel_iff e,
    MulEquiv.apply_symm_apply]

/-! ### The action on the discriminant quadratic module -/

/-- For an even nondegenerate lattice `L`, the action of `O(L)` on the discriminant group preserves
the discriminant quadratic form `q_L`, giving a homomorphism `O(L) →* O(q_L)`. -/
noncomputable def discriminantOrthogonalHom (L : IntegralLattice V) [L.IsNondegenerate]
    (hL : L.IsEven) :
    Isometry L L →* FiniteQuadraticModule.orthogonalGroup (L.discriminantQuadraticModule hL) :=
  (discriminantGroupHom L).codRestrict _ fun g ↦
    QuadraticMap.mem_orthogonalGroup_iff.mpr fun a ↦
      (congrArg (L.discriminantQuadraticModule hL).quadratic
        (g.discriminantQuadraticIsometry_apply hL a)).symm.trans
          ((g.discriminantQuadraticIsometry hL).map_app a)

/-- The homomorphism `O(L) →* O(q_L)` acts through the discriminant-group action. -/
@[simp]
theorem coe_discriminantOrthogonalHom [L.IsNondegenerate] (hL : L.IsEven) (g : Isometry L L) :
    (discriminantOrthogonalHom L hL g :
        L.discriminantQuadraticModule hL ≃ₗ[ℤ] L.discriminantQuadraticModule hL) =
      discriminantGroupHom L g :=
  (rfl)

/-- Negation is sent to the negation element of `O(q_L)`. -/
@[simp]
theorem discriminantOrthogonalHom_neg [L.IsNondegenerate] (hL : L.IsEven) :
    discriminantOrthogonalHom L hL (neg L) =
      QuadraticMap.negOrthogonal (L.discriminantQuadraticModule hL).quadratic :=
  Subtype.ext <| LinearEquiv.ext fun a ↦ by
    simp only [coe_discriminantOrthogonalHom, discriminantGroupHom_apply,
      discriminantGroupEquiv_neg, QuadraticMap.coe_negOrthogonal]
    exact LinearEquiv.neg_apply a

/-- The kernel of `O(L) →* O(q_L)` is the discriminant kernel. -/
@[simp]
theorem ker_discriminantOrthogonalHom [L.IsNondegenerate] (hL : L.IsEven) :
    (discriminantOrthogonalHom L hL).ker = discriminantKernel L :=
  MonoidHom.ker_codRestrict _ _ _

end Isometry

variable {V : Type*} [AddCommGroup V] [Module ℚ V]

/-- A unimodular lattice has trivial discriminant group, so every self-isometry lies in its
discriminant kernel. -/
theorem IsUnimodular.discriminantKernel_eq_top {L : IntegralLattice V} (hL : L.IsUnimodular) :
    Isometry.discriminantKernel L = ⊤ := by
  have := L.isUnimodular_iff_subsingleton_discriminantGroup.mp hL
  rw [eq_top_iff]
  intro g _
  rw [Isometry.discriminantKernel, MonoidHom.mem_ker]
  exact LinearEquiv.ext fun a ↦ Subsingleton.elim _ _

end IntegralLattice

end TauCeti
