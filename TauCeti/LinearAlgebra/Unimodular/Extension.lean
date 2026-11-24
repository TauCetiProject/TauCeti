/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import Mathlib.Algebra.Module.StablyFree.Basic
public import Mathlib.LinearAlgebra.Dimension.Free
public import Mathlib.LinearAlgebra.GeneralLinearGroup.Basic
public import Mathlib.LinearAlgebra.Matrix.Action
public import Mathlib.LinearAlgebra.Matrix.GeneralLinearGroup.Defs
public import Mathlib.LinearAlgebra.Transvection.Basic
public import TauCeti.LinearAlgebra.Prod
public import TauCeti.LinearAlgebra.Basis.Fin
public import TauCeti.LinearAlgebra.Unimodular

/-!
# Equivalence of unimodular vectors and the unimodular extension property

Two vectors `v w : ι → R` are *equivalent*, `TauCeti.UnimodularEquiv v w`, when an invertible
matrix carries one to the other: `P *ᵥ v = w` for some `P : GL ι R`. A commutative ring `R` has
the *unimodular extension property*, `TauCeti.HasUnimodularExtension R`, when every unimodular
vector `v : Fin (n + 1) → R` (its entries generate the unit ideal) is equivalent to the first
standard basis vector `Pi.single 0 1`; equivalently, every unimodular vector is the first column
of an invertible matrix, or the first vector of a basis of `Fin (n + 1) → R`.

The main theorem is `TauCeti.hasUnimodularExtension_iff`: `R` has the unimodular extension
property if and only if every finite stably free `R`-module is free (Lang, *Algebra*, XXI.3.6,
for the forward direction). Together with Horrocks' theorem over polynomial rings this is the
algebraic input of the rigid-analytic Quillen–Suslin theorem, where a finite projective module
is first shown to be stably free and then free.

## Main definitions

* `TauCeti.UnimodularEquiv v w`: some `P : GL ι R` has `P *ᵥ v = w`.
* `TauCeti.HasUnimodularExtension R`: every unimodular `v : Fin (n + 1) → R` is equivalent to
  `Pi.single 0 1`.

## Main results

* `TauCeti.UnimodularEquiv.equivalence`, `TauCeti.unimodularEquiv_iff_mem_orbit`: equivalence of
  vectors is an equivalence relation, namely lying in one orbit of `GL ι R`.
* `TauCeti.unimodularEquiv_iff_exists_linearEquiv`: equivalent vectors are those related by a
  linear automorphism of `ι → R`; `TauCeti.unimodularEquiv_single_iff_exists_basis`: a vector is
  equivalent to `Pi.single i 1` iff it is the `i`-th vector of a basis.
* `TauCeti.UnimodularEquiv.isUnimodular_iff`, `TauCeti.UnimodularEquiv.map`: equivalence
  preserves unimodularity and is carried along ring homomorphisms.
* `TauCeti.UnimodularEquiv.of_apply_eq_one`: two vectors at which a common linear functional takes
  the value `1` are equivalent, by a transvection.
* `TauCeti.unimodularEquiv_single_of_isUnit`: a vector with a unit entry is equivalent to every
  standard basis vector; `TauCeti.unimodularEquiv_single_zero_of_fin_two`: so is every unimodular
  vector of length two.
* `IsLocalRing.hasUnimodularExtension`: local rings, in particular fields, have the unimodular
  extension property; `RingEquiv.hasUnimodularExtension_iff`: the property is invariant under
  ring isomorphisms.
* `TauCeti.HasUnimodularExtension.free_of_isStablyFree`: under the unimodular extension property,
  every finite stably free module is free.
* `TauCeti.hasUnimodularExtension_iff`: the unimodular extension property holds iff every finite
  stably free module is free.

## References

* S. Lang, *Algebra*, 3rd ed., GTM 211, Springer, 2002, Chapter XXI, §3, Theorem 3.6.
* K. S. Kedlaya, *Full faithfulness for overconvergent F-isocrystals*, Propositions 6.4 and 6.6,
  which apply it to Monsky–Washnitzer algebras.
-/

public section

noncomputable section

open Matrix Module

universe u

namespace TauCeti

variable {R ι : Type*}

/-! ### Equivalence of vectors -/

section Semiring

variable [Semiring R] [Fintype ι] [DecidableEq ι]

/-- Two vectors `v w : ι → R` are *equivalent* when some invertible matrix `P` carries `v` to `w`,
`P *ᵥ v = w`. -/
def UnimodularEquiv (v w : ι → R) : Prop :=
  ∃ P : GL ι R, (P : Matrix ι ι R) *ᵥ v = w

/-- Restatement of the definition of `TauCeti.UnimodularEquiv`. -/
theorem unimodularEquiv_iff {v w : ι → R} :
    UnimodularEquiv v w ↔ ∃ P : GL ι R, (P : Matrix ι ι R) *ᵥ v = w :=
  Iff.rfl

/-- Two vectors are equivalent exactly when they lie in one orbit of `GL ι R`, acting on
`ι → R` through `Matrix.mulVec`. -/
theorem unimodularEquiv_iff_mem_orbit {v w : ι → R} :
    UnimodularEquiv v w ↔ w ∈ MulAction.orbit (GL ι R) v := by
  simp [unimodularEquiv_iff, MulAction.mem_orbit_iff, Units.smul_def]

namespace UnimodularEquiv

/-- Every vector is equivalent to itself. -/
@[refl]
theorem refl (v : ι → R) : UnimodularEquiv v v :=
  ⟨1, by simp⟩

/-- Every vector is equivalent to itself (implicit-argument form of `refl`). -/
theorem rfl {v : ι → R} : UnimodularEquiv v v :=
  refl v

/-- Equivalence of vectors is symmetric. -/
@[symm]
theorem symm {v w : ι → R} (h : UnimodularEquiv v w) : UnimodularEquiv w v := by
  obtain ⟨P, rfl⟩ := h
  exact ⟨P⁻¹, by simp [mulVec_mulVec]⟩

/-- Equivalence of vectors is symmetric, as an `Iff`. -/
theorem comm {v w : ι → R} : UnimodularEquiv v w ↔ UnimodularEquiv w v :=
  ⟨symm, symm⟩

/-- Equivalence of vectors is transitive. -/
@[trans]
theorem trans {u v w : ι → R} (huv : UnimodularEquiv u v) (hvw : UnimodularEquiv v w) :
    UnimodularEquiv u w := by
  obtain ⟨P, rfl⟩ := huv
  obtain ⟨Q, rfl⟩ := hvw
  exact ⟨Q * P, by rw [Units.val_mul, mulVec_mulVec]⟩

variable (R ι) in
/-- Equivalence of vectors is an equivalence relation. -/
theorem equivalence : Equivalence (UnimodularEquiv (R := R) (ι := ι)) :=
  ⟨refl, symm, trans⟩

end UnimodularEquiv

end Semiring

section CommRing

variable [CommRing R] [Fintype ι] [DecidableEq ι]

/-- Two vectors are equivalent exactly when a linear automorphism of `ι → R` carries one to the
other. -/
theorem unimodularEquiv_iff_exists_linearEquiv {v w : ι → R} :
    UnimodularEquiv v w ↔ ∃ g : (ι → R) ≃ₗ[R] (ι → R), g v = w := by
  constructor
  · rintro ⟨P, rfl⟩
    refine ⟨(GeneralLinearGroup.toLin P).toLinearEquiv, ?_⟩
    simp [LinearMap.GeneralLinearGroup.toLinearEquiv]
  · rintro ⟨g, rfl⟩
    refine ⟨GeneralLinearGroup.toLin.symm (LinearMap.GeneralLinearGroup.ofLinearEquiv g), ?_⟩
    rw [← mulVecLin_apply, ← GeneralLinearGroup.toLin_apply, MulEquiv.apply_symm_apply]
    simp

namespace UnimodularEquiv

/-- Equivalent vectors are unimodular together. -/
theorem isUnimodular_iff {v w : ι → R} (h : UnimodularEquiv v w) :
    IsUnimodular R v ↔ IsUnimodular R w := by
  obtain ⟨g, rfl⟩ := unimodularEquiv_iff_exists_linearEquiv.mp h
  exact g.isUnimodular_apply_iff.symm

/-- Equivalence of vectors is carried along a ring homomorphism applied to the entries. -/
theorem map {S : Type*} [CommRing S] (f : R →+* S) {v w : ι → R} (h : UnimodularEquiv v w) :
    UnimodularEquiv (f ∘ v) (f ∘ w) := by
  obtain ⟨P, rfl⟩ := h
  refine ⟨GeneralLinearGroup.map f P, funext fun i ↦ ?_⟩
  simp [RingHom.map_mulVec]

/-- Two vectors at which a common linear functional takes the value `1` are equivalent. -/
theorem of_apply_eq_one {f : (ι → R) →ₗ[R] R} {v w : ι → R} (hv : f v = 1) (hw : f w = 1) :
    UnimodularEquiv v w := by
  -- The transvection `x ↦ x + f x • (w - v)` carries `v` to `w`.
  have hfvw : f (w - v) = 0 := by rw [map_sub, hv, hw, sub_self]
  exact unimodularEquiv_iff_exists_linearEquiv.mpr
    ⟨LinearEquiv.transvection hfvw, by
      rw [LinearEquiv.transvection.apply, hv, one_smul, add_sub_cancel]⟩

/-- Multiplying a vector by a unit gives an equivalent vector. -/
theorem units_smul_left (c : Rˣ) (v : ι → R) : UnimodularEquiv (c • v) v :=
  unimodularEquiv_iff_exists_linearEquiv.mpr
    ⟨LinearEquiv.smulOfUnit c⁻¹, inv_smul_smul c v⟩

end UnimodularEquiv

/-- Any two standard basis vectors are equivalent. -/
theorem unimodularEquiv_single_single (i j : ι) :
    UnimodularEquiv (Pi.single i (1 : R)) (Pi.single j 1) := by
  rcases eq_or_ne i j with rfl | hij
  · rfl
  · exact .of_apply_eq_one (f := (LinearMap.proj i : (ι → R) →ₗ[R] R) + LinearMap.proj j)
      (by simp [Pi.single_eq_of_ne hij.symm]) (by simp [Pi.single_eq_of_ne hij])

/-- A vector with a unit entry is equivalent to every standard basis vector. -/
theorem unimodularEquiv_single_of_isUnit {v : ι → R} {i : ι} (hi : IsUnit (v i)) (j : ι) :
    UnimodularEquiv v (Pi.single j 1) := by
  let f : (ι → R) →ₗ[R] R := (↑hi.unit⁻¹ : R) • LinearMap.proj i
  have hv : f v = 1 := by simp [f]
  have hsingle : f (Pi.single i (v i)) = 1 := by simp [f]
  refine (UnimodularEquiv.of_apply_eq_one hv hsingle).trans
    (.trans ?_ (unimodularEquiv_single_single i j))
  have hsmul : Pi.single i (v i) = hi.unit • (Pi.single i 1 : ι → R) := by
    simp [Units.smul_def, ← Pi.single_smul]
  rw [hsmul]
  exact .units_smul_left _ _

/-- A vector is equivalent to the standard basis vector `Pi.single i 1` exactly when it is the
`i`-th vector of a basis of `ι → R`, that is, the `i`-th column of an invertible matrix. -/
theorem unimodularEquiv_single_iff_exists_basis {v : ι → R} (i : ι) :
    UnimodularEquiv v (Pi.single i 1) ↔ ∃ b : Basis ι R (ι → R), b i = v := by
  rw [UnimodularEquiv.comm, unimodularEquiv_iff_exists_linearEquiv]
  constructor
  · rintro ⟨g, rfl⟩
    exact ⟨(Pi.basisFun R ι).map g, by simp⟩
  · rintro ⟨b, rfl⟩
    exact ⟨(Pi.basisFun R ι).equiv b (Equiv.refl ι), by
      simpa using (Pi.basisFun R ι).equiv_apply i b (Equiv.refl ι)⟩

/-- Every unimodular vector of length two is equivalent to `Pi.single 0 1`. This is
`Module.IsUnimodular.exists_basis_zero_eq` for `Fin 2 → R`. -/
theorem unimodularEquiv_single_zero_of_fin_two {v : Fin 2 → R} (hv : IsUnimodular R v) :
    UnimodularEquiv v (Pi.single 0 1) := by
  cases subsingleton_or_nontrivial R
  · exact Subsingleton.elim v (Pi.single 0 1) ▸ .rfl
  obtain ⟨b, hb⟩ := hv.exists_basis_zero_eq (Module.finrank_fin_fun R)
  exact (unimodularEquiv_single_iff_exists_basis 0).mpr ⟨b, hb⟩

end CommRing

/-! ### The unimodular extension property -/

variable (R) in
/-- A commutative ring `R` has the *unimodular extension property* when every unimodular vector
`v : Fin (n + 1) → R` is equivalent to the first standard basis vector `Pi.single 0 1`;
equivalently (`TauCeti.unimodularEquiv_single_iff_exists_basis`), every unimodular vector is the
first column of an invertible matrix. -/
def HasUnimodularExtension [CommRing R] : Prop :=
  ∀ (n : ℕ) (v : Fin (n + 1) → R), IsUnimodular R v → UnimodularEquiv v (Pi.single 0 1)

section CommRing

variable [CommRing R]

/-- Restatement of the definition of `TauCeti.HasUnimodularExtension`. -/
theorem hasUnimodularExtension_def : HasUnimodularExtension R ↔
    ∀ (n : ℕ) (v : Fin (n + 1) → R), IsUnimodular R v → UnimodularEquiv v (Pi.single 0 1) :=
  Iff.rfl

/-- Over the zero ring every vector equals `Pi.single 0 1`, so the property holds. -/
theorem hasUnimodularExtension_of_subsingleton [Subsingleton R] : HasUnimodularExtension R :=
  fun _ v _ ↦ Subsingleton.elim v (Pi.single 0 1) ▸ .rfl

/-- Local rings, in particular fields, have the unimodular extension property. -/
theorem _root_.IsLocalRing.hasUnimodularExtension [IsLocalRing R] : HasUnimodularExtension R :=
  -- A unimodular vector over a local ring has a unit entry.
  fun _ _ hv ↦
    let ⟨_, hi⟩ := Module.isUnimodular_iff_exists_isUnit.mp hv
    unimodularEquiv_single_of_isUnit hi 0

/-- The unimodular extension property passes along a ring isomorphism. -/
theorem HasUnimodularExtension.of_ringEquiv {S : Type*} [CommRing S] (e : R ≃+* S)
    (h : HasUnimodularExtension R) : HasUnimodularExtension S := by
  intro n v hv
  have hv' : IsUnimodular R (e.symm ∘ v) := hv.ringHom_comp e.symm.toRingHom
  have key := (h n _ hv').map e.toRingHom
  have hsingle : (e.toRingHom ∘ Pi.single 0 1 : Fin (n + 1) → S) = Pi.single 0 1 := by
    ext k
    rcases eq_or_ne k 0 with rfl | hk <;> simp [*]
  rw [hsingle] at key
  convert key using 1
  ext k
  simp

/-- The unimodular extension property is invariant under ring isomorphisms. -/
theorem _root_.RingEquiv.hasUnimodularExtension_iff {S : Type*} [CommRing S] (e : R ≃+* S) :
    HasUnimodularExtension R ↔ HasUnimodularExtension S :=
  ⟨.of_ringEquiv e, .of_ringEquiv e.symm⟩

namespace HasUnimodularExtension

variable (h : HasUnimodularExtension R)
include h

/-- Under the unimodular extension property a free factor `R` cancels: if `M` is finite and
`M × R` is free, then `M` is free. -/
theorem free_of_free_prod (M : Type*) [AddCommGroup M] [Module R M] [Module.Finite R M]
    [Module.Free R (M × R)] : Module.Free R M := by
  -- The image `v` of `(0, 1)` under a basis isomorphism `M × R ≃ Rⁿ⁺¹` is unimodular, so an
  -- automorphism of `Rⁿ⁺¹` moves it to `Pi.single 0 1`; the resulting isomorphism
  -- `M × R ≃ Rⁿ × R` fixes the factor `R`, which then cancels.
  cases subsingleton_or_nontrivial R
  · exact Module.Free.of_subsingleton' R M
  have hpos : finrank R (M × R) ≠ 0 := ((finrank_pos_iff_of_free R (M × R)).mpr inferInstance).ne'
  obtain ⟨n, hn⟩ := Nat.exists_eq_succ_of_ne_zero hpos
  let e : (M × R) ≃ₗ[R] (Fin (n + 1) → R) := (finBasisOfFinrankEq R (M × R) hn).equivFun
  have hv : IsUnimodular R (e (0, 1)) :=
    isUnimodular_of_apply_eq_one (f := LinearMap.snd R M R ∘ₗ e.symm.toLinearMap) (by simp)
  obtain ⟨g, hg⟩ := unimodularEquiv_iff_exists_linearEquiv.mp (h n _ hv)
  let φ : (M × R) ≃ₗ[R] ((Fin n → R) × R) :=
    ((e.trans g).trans (Fin.consLinearEquiv R fun _ : Fin (n + 1) ↦ R).symm).trans
      (LinearEquiv.prodComm R R (Fin n → R))
  -- `φ` fixes `(0, 1)`, so its lower-right block `R → R` is the identity.
  have hφ : φ (0, 1) = (0, 1) := by
    simp only [φ, LinearEquiv.trans_apply, hg]
    ext k <;> simp [Fin.tail]
  have hblock : (LinearMap.snd R (Fin n → R) R).comp
      ((φ : (M × R) →ₗ[R] ((Fin n → R) × R)).comp (LinearMap.inr R M R)) = LinearMap.id := by
    ext
    simp [hφ]
  obtain ⟨ψ⟩ := LinearEquiv.nonempty_linearEquiv_of_isUnit_snd_comp_inr φ
    (hblock ▸ isUnit_one)
  exact Module.Free.of_equiv ψ.symm

/-- Under the unimodular extension property, every finite stably free module is free (Lang,
*Algebra*, XXI.3.6). -/
theorem free_of_isStablyFree (M : Type*) [AddCommGroup M] [Module R M] [Module.Finite R M]
    [IsStablyFree R M] : Module.Free R M := by
  -- Cancel the free complement `Rᵏ` one factor at a time with `free_of_free_prod`.
  cases subsingleton_or_nontrivial R
  · exact Module.Free.of_subsingleton' R M
  obtain ⟨N, _, _, _, _, _⟩ := IsStablyFree.exist_free_prod R M
  suffices hk : ∀ k : ℕ, Module.Free R (M × (Fin k → R)) → Module.Free R M from
    hk _ (Module.Free.of_equiv
      ((LinearEquiv.refl R M).prodCongr (finBasis R N).equivFun))
  intro k
  induction k with
  | zero =>
    intro _
    exact Module.Free.of_equiv (LinearEquiv.prodUnique (R := R) (M := M) (M₂ := Fin 0 → R))
  | succ k ih =>
    intro hfree
    have : Module.Free R ((M × (Fin k → R)) × R) :=
      Module.Free.of_equiv
        ((((LinearEquiv.refl R M).prodCongr (Fin.consLinearEquiv R fun _ : Fin (k + 1) ↦ R).symm)
          |>.trans ((LinearEquiv.refl R M).prodCongr (LinearEquiv.prodComm R R (Fin k → R)))
          |>.trans (LinearEquiv.prodAssoc R M (Fin k → R) R).symm))
    exact ih (h.free_of_free_prod _)

end HasUnimodularExtension

/-- If every finite stably free `R`-module is free, then `R` has the unimodular extension
property. -/
theorem hasUnimodularExtension_of_forall_free {R : Type u} [CommRing R]
    (h : ∀ (M : Type u) [AddCommGroup M] [Module R M], Module.Finite R M → IsStablyFree R M →
      Module.Free R M) :
    HasUnimodularExtension R := by
  -- For a unimodular `v` with `f v = 1`, the kernel `K` of `f` satisfies `K × R ≃ Rⁿ⁺¹`, so it is
  -- stably free, hence free of rank `n`, and `v` followed by a basis of `K` is a basis of `Rⁿ⁺¹`.
  intro n v hv
  cases subsingleton_or_nontrivial R
  · exact hasUnimodularExtension_of_subsingleton n v hv
  obtain ⟨f, hf⟩ := isUnimodular_iff.mp hv
  let K := LinearMap.ker f
  let e : (K × R) ≃ₗ[R] (Fin (n + 1) → R) := LinearMap.kerProdEquivOfApplyEqOne hf
  have : Module.Free R (K × R) := Module.Free.of_equiv e.symm
  have : Module.Finite R (K × R) := Module.Finite.equiv e.symm
  have : Module.Finite R K :=
    Module.Finite.of_surjective (LinearMap.fst R K R) LinearMap.fst_surjective
  have : IsStablyFree R K := IsStablyFree.of_free_prod R K R
  have : Module.Free R K := h K inferInstance inferInstance
  have hrank : finrank R K = n := by
    have := e.finrank_eq
    rw [Module.finrank_prod, Module.finrank_self, Module.finrank_fin_fun] at this
    omega
  obtain ⟨c, hc, -⟩ := Basis.exists_basis_finCons_of_apply_eq_one hf
    (finBasisOfFinrankEq R K hrank)
  exact (unimodularEquiv_single_iff_exists_basis 0).mpr ⟨c, hc⟩

/-- **Unimodular extension and stably free modules.** A commutative ring has the unimodular
extension property exactly when every finite stably free module over it is free (Lang, *Algebra*,
XXI.3.6, for the forward direction). -/
theorem hasUnimodularExtension_iff {R : Type u} [CommRing R] :
    HasUnimodularExtension R ↔ ∀ (M : Type u) [AddCommGroup M] [Module R M],
      Module.Finite R M → IsStablyFree R M → Module.Free R M :=
  ⟨fun h _ _ _ _ _ ↦ h.free_of_isStablyFree _, hasUnimodularExtension_of_forall_free⟩

end CommRing

end TauCeti
