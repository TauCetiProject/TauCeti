/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import Mathlib.Algebra.Module.Torsion.Basic
public import Mathlib.RingTheory.Flat.Basic
public import Mathlib.RingTheory.Jacobson.Ideal
public import Mathlib.RingTheory.LocalRing.RingHom.Basic
public import Mathlib.RingTheory.QuotSMulTop
public import Mathlib.RingTheory.RingHom.Flat
import Mathlib.LinearAlgebra.TensorProduct.RightExactness
import Mathlib.RingTheory.Filtration
import Mathlib.RingTheory.Flat.Stability
import Mathlib.RingTheory.Flat.Tensor
import Mathlib.RingTheory.TensorProduct.Quotient
import Mathlib.Tactic.Algebraize
import TauCeti.LinearAlgebra.TensorProduct.Submodule
import TauCeti.RingTheory.Ideal.TensorProduct
import TauCeti.RingTheory.TensorProduct.Finite

/-!
# The local criterion for flatness

Let `R` be a Noetherian ring, `S` a Noetherian `R`-algebra, `M` a finite `S`-module and `I` an
ideal of `R` whose extension `I S` lies in the Jacobson radical of `S`. If `I ⊗[R] M → M` is
injective, that is `Tor₁ᴿ(R ⧸ I, M) = 0`, and `M ⧸ I M` is flat over `R ⧸ I`, then `M` is flat
over `R` (`Module.Flat.of_subtype_rTensor_injective`). This is the local criterion for flatness
(Stacks, Tag 00MK), stated with the Jacobson radical in place of a local homomorphism of local
rings. For a local homomorphism `R → S` and `I` the maximal ideal of `R`, the quotient `M ⧸ I M`
is a vector space over the residue field, so flatness of `M` reduces to the vanishing of
`Tor₁ᴿ(κ, M)`.

Two special cases are derived.

* **A regular element** (Stacks, Tag 00ML, for the ideal `(x)`). If `x ∈ R` is `M`-regular, then
  `Tor₁ᴿ(R ⧸ (x), M) = 0` (`IsSMulRegular.subtype_rTensor_injective_span`), so `M` is flat over `R`
  as soon as `M ⧸ x M` is flat over `R ⧸ (x)` (`Module.Flat.of_flat_quotSMulTop`). Conversely
  `M ⧸ x M` is flat over `R ⧸ (x)` whenever `M` is flat over `R`, so for an `M`-regular `x` the two
  conditions are equivalent (`Module.flat_quotSMulTop_iff_flat`), the flat counterpart of
  Mathlib's `Module.free_quotSMulTop_iff_free`. This is the inductive step of miracle flatness
  (Stacks, Tag 00R4).
* **Flatness over the fibres** (Stacks, Tag 00MP). Let `R → S → T` be ring maps with `S` and `T`
  Noetherian, `M` a finite `T`-module flat over `R`, and `J` an ideal of `R` with `J T` in the
  Jacobson radical of `T`. Flatness over `R` already gives `Tor₁ˢ(S ⧸ J S, M) = 0`
  (`Module.Flat.subtype_rTensor_injective_map`), so `M` is flat over `S` as soon as `M ⧸ J M` is
  flat over `S ⧸ J S` (`Module.Flat.of_flat_quotient_map`). For local rings and `J` the maximal
  ideal of `R`, the fibre condition holds automatically when `J S` is the maximal ideal of `S`;
  in ring homomorphism form, `f : S → T` is flat as soon as `f ∘ g` is, for some `g : R → S` with
  `𝔪_R S = 𝔪_S` (`RingHom.Flat.of_comp_of_map_maximalIdeal_eq`). The typical `g` is the map to
  the completion of a Noetherian local ring, which transports flatness of an endomorphism such as
  Frobenius to the completion.

## Implementation notes

By Mathlib's ideal criterion it suffices that `M ⊗[R] J → M` is injective for every ideal `J`.

1. Tensoring with `M` preserves injectivity of maps between modules killed by `I`: over `R ⧸ I`
   this is flatness of `M ⧸ I M`, transported along `K ⊗[R ⧸ I] (R ⧸ I ⊗[R] M) ≃ K ⊗[R] M`.
2. If `L ⧸ N` is killed by `I`, then `N ⊗[R] M → L ⊗[R] M` is injective. Cover `L` by a free
   module `F` and let `G` be the preimage of `N`; then `G ⊇ I F`, and `I F ⊗ M → F ⊗ M` is
   injective because `F` is flat and `I ⊗ M → M` is injective. Two diagram chases replace the
   long exact `Tor` sequences of the textbook proof.
3. By induction, the same holds when `L ⧸ N` is killed by `Iⁿ`. Applied to `J ⧸ (J ⊓ Iⁿ)` inside
   `R ⧸ Iⁿ`, it shows that the kernel of `J ⊗[R] M → M` comes from `(J ⊓ Iⁿ) ⊗[R] M`.
4. By the Artin–Rees lemma `J ⊓ Iⁿ ⊆ I^(n - c) J`, so an element `t` of the kernel lies in
   `I^(n - c) (M ⊗[R] J)` for all `n`. Since `M ⊗[R] J` is a finite `S`-module
   (`Module.Finite.tensor`), Krull's intersection theorem over `S` gives `t = 0`.

## Main results

* `Module.Flat.of_subtype_rTensor_injective`: the local criterion for flatness.
* `Module.Flat.subtype_rTensor_injective_map`: an `S`-module that is flat over `R` has
  `Tor₁ˢ(S ⧸ J S, M) = 0` for every ideal `J` of `R`.
* `Module.Flat.of_flat_quotient_map`: the criterion for flatness over the fibres.
* `RingHom.Flat.of_comp_of_map_maximalIdeal_eq`: `f` is flat if `f ∘ g` is flat and `g` maps the
  maximal ideal onto the maximal ideal.
* `Module.Flat.of_flat_quotSMulTop`: the criterion along a regular element.
* `Module.Flat.quotSMulTop`: `M ⧸ x M` is flat over `R ⧸ (x)` when `M` is flat over `R`.
* `Module.flat_quotSMulTop_iff_flat`: for an `M`-regular `x` as above, `M ⧸ x M` is flat over
  `R ⧸ (x)` if and only if `M` is flat over `R`.

## References

* [The Stacks Project, Tag 00MK](https://stacks.math.columbia.edu/tag/00MK), the local criterion
  for flatness, and Tag 00ML, its variant along a regular element.
* [The Stacks Project, Tag 00MP](https://stacks.math.columbia.edu/tag/00MP), flatness over the
  fibres.
* [The Stacks Project, Tag 00R4](https://stacks.math.columbia.edu/tag/00R4), miracle flatness,
  whose proof uses the criterion along a regular element.
* H. Matsumura, *Commutative Ring Theory*, Theorems 22.3 and 22.5.
-/

public section

open TensorProduct LinearMap

namespace Module

variable {R M : Type*} [CommRing R] [AddCommGroup M] [Module R M]

/-- If `M` is flat over `R`, then `M ⧸ x M` is flat over `R ⧸ (x)`. -/
instance Flat.quotSMulTop [Flat R M] (x : R) : Flat (R ⧸ Ideal.span {x}) (QuotSMulTop x M) :=
  .of_linearEquiv ((QuotSMulTop.equivQuotTensor x M).extendScalarsOfSurjective
    Ideal.Quotient.mk_surjective)

/-! ### The local criterion -/

/-- If `M ⧸ I M` is flat over `R ⧸ I`, tensoring with `M` preserves injectivity of maps between
modules killed by `I`. -/
private theorem rTensor_injective_of_isTorsionBySet (I : Ideal R)
    [Flat (R ⧸ I) (M ⧸ I • (⊤ : Submodule R M))] {K L : Type*} [AddCommGroup K] [Module R K]
    [AddCommGroup L] [Module R L] (hK : IsTorsionBySet R K I) (hL : IsTorsionBySet R L I)
    {f : K →ₗ[R] L} (hf : Function.Injective f) : Function.Injective (f.rTensor M) := by
  let _ := hK.module
  let _ := hL.module
  let A := R ⧸ I
  have hA : Function.Surjective (algebraMap R A) := Ideal.Quotient.mk_surjective
  let g : K →ₗ[A] L := f.extendScalarsOfSurjective hA
  have : Flat A (A ⊗[R] M) := .of_linearEquiv
    ((quotTensorEquivQuotSMul M I).extendScalarsOfSurjective hA)
  let eK := AlgebraTensorModule.cancelBaseChange R A A K M
  let eL := AlgebraTensorModule.cancelBaseChange R A A L M
  have key (y : K ⊗[A] (A ⊗[R] M)) : f.rTensor M (eK y) = eL (g.rTensor _ y) := by
    induction y using TensorProduct.inductionOn with
    | add y z hy hz => simp only [map_add, hy, hz]
    | tmul k t =>
      induction t using TensorProduct.inductionOn with
      | add s t hs ht => simp only [tmul_add, map_add, hs, ht]
      | tmul a m =>
        simp only [eK, eL, AlgebraTensorModule.cancelBaseChange_tmul, rTensor_tmul]
        rw [← map_smul g]
        rfl
  intro x y hxy
  obtain ⟨x, rfl⟩ := eK.surjective x
  obtain ⟨y, rfl⟩ := eK.surjective y
  rw [key, key, eL.injective.eq_iff] at hxy
  rw [Flat.rTensor_preserves_injective_linearMap g hf hxy]

/-- If `I ⊗[R] M → M` is injective and `F` is flat, then `(I ⊗[R] F) ⊗[R] M → F ⊗[R] M` is
injective. -/
private theorem rTensor_injective_smul_of_flat {I : Ideal R}
    (hI : Function.Injective (I.subtype.rTensor M))
    (F : Type*) [AddCommGroup F] [Module R F] [Flat R F] :
    Function.Injective
      (((TensorProduct.lid R F).toLinearMap ∘ₗ I.subtype.rTensor F).rTensor M) := by
  have h : (rightComm R R F M).toLinearMap ∘ₗ (I.subtype.rTensor F).rTensor M =
      ((I.subtype.rTensor M).rTensor F) ∘ₗ (rightComm R I F M).toLinearMap := by
    ext; rfl
  have hY : Function.Injective ((I.subtype.rTensor M).rTensor F ∘ₗ
      (rightComm R I F M).toLinearMap) :=
    (Flat.rTensor_preserves_injective_linearMap _ hI).comp (rightComm R I F M).injective
  rw [← h, coe_comp] at hY
  rw [rTensor_comp, coe_comp]
  exact (LinearEquiv.rTensor M (TensorProduct.lid R F)).injective.comp hY.of_comp

section

variable {I : Ideal R} [Flat (R ⧸ I) (M ⧸ I • (⊤ : Submodule R M))]

/-- For a flat module `F`, a submodule `G ⊇ I F` has `G ⊗[R] M → F ⊗[R] M` injective. -/
private theorem subtype_rTensor_injective_of_flat
    (hI : Function.Injective (I.subtype.rTensor M))
    {F : Type*} [AddCommGroup F] [Module R F] [Flat R F] {G : Submodule R F} (hIG : I • ⊤ ≤ G) :
    Function.Injective (G.subtype.rTensor M) := by
  -- The image of `I ⊗ F` in `F` is `I F ⊆ G`, and `G ⧸ I F` is a submodule of `F ⧸ I F`, a module
  -- killed by `I`.
  let φ : I ⊗[R] F →ₗ[R] F := (TensorProduct.lid R F).toLinearMap ∘ₗ I.subtype.rTensor F
  have hφ : range φ = I • ⊤ := I.subtype_rTensor_range F
  let μ : I ⊗[R] F →ₗ[R] G := φ.codRestrict G fun x ↦ hIG (hφ ▸ mem_range_self φ x)
  let K : Submodule R (F ⧸ (I • ⊤ : Submodule R F)) := G.map (I • ⊤ : Submodule R F).mkQ
  let q : G →ₗ[R] K := ((I • ⊤ : Submodule R F).mkQ ∘ₗ G.subtype).codRestrict K
    fun g ↦ Submodule.mem_map_of_mem g.2
  have hq : Function.Surjective q := by
    rintro ⟨_, g, hg, rfl⟩
    exact ⟨⟨g, hg⟩, rfl⟩
  have hμq : Function.Exact μ q := by
    intro g
    rw [← Subtype.coe_inj, ZeroMemClass.coe_zero]
    simp only [q, codRestrict_apply, coe_comp, Function.comp_apply, Submodule.mkQ_apply,
      Submodule.coe_subtype, Submodule.Quotient.mk_eq_zero]
    rw [← hφ]
    exact ⟨fun ⟨u, hu⟩ ↦ ⟨u, Subtype.ext hu⟩, fun ⟨u, hu⟩ ↦ ⟨u, congr_arg Subtype.val hu⟩⟩
  have hK : IsTorsionBySet R K I := fun x i ↦
    Subtype.ext (isTorsionBySet_quotient_ideal_smul F I (x := x.1) (a := i))
  have hKinj := rTensor_injective_of_isTorsionBySet (M := M) I hK
    (isTorsionBySet_quotient_ideal_smul F I) K.injective_subtype
  refine (injective_iff_map_eq_zero _).mpr fun t ht ↦ ?_
  have hqt : q.rTensor M t = 0 := hKinj <| by
    rw [← rTensor_comp_apply, map_zero]
    have : K.subtype ∘ₗ q = (I • ⊤ : Submodule R F).mkQ ∘ₗ G.subtype := rfl
    rw [this, rTensor_comp_apply, ht, map_zero]
  obtain ⟨u, rfl⟩ := (rTensor_exact M hμq hq t).mp hqt
  have hu : φ.rTensor M u = 0 := by
    rw [← ht, ← rTensor_comp_apply]
    rfl
  rw [rTensor_injective_smul_of_flat hI F (hu.trans (map_zero _).symm), map_zero]

/-- If `L ⧸ N` is killed by `I`, then `N ⊗[R] M → L ⊗[R] M` is injective; the proof chases along
a flat module `F` mapping onto `L`. -/
private theorem subtype_rTensor_injective_of_surjective
    (hI : Function.Injective (I.subtype.rTensor M))
    {F L : Type*} [AddCommGroup F] [Module R F] [Flat R F] [AddCommGroup L] [Module R L]
    {π : F →ₗ[R] L} (hπ : Function.Surjective π) {N : Submodule R L} (hN : I • ⊤ ≤ N) :
    Function.Injective (N.subtype.rTensor M) := by
  have hIG : I • ⊤ ≤ N.comap π := Submodule.map_le_iff_le_comap.mp <| by
    rw [Submodule.map_smul'']
    exact (Submodule.smul_mono le_rfl le_top).trans hN
  have hG := subtype_rTensor_injective_of_flat hI hIG
  -- A diagram chase along `π`.
  let π' : N.comap π →ₗ[R] N := π.restrict fun _ hx ↦ hx
  have hπ' : Function.Surjective π' := fun n ↦
    let ⟨x, hx⟩ := hπ n
    ⟨⟨x, Submodule.mem_comap.mpr (hx ▸ n.2)⟩, Subtype.ext hx⟩
  have hsq : π ∘ₗ (N.comap π).subtype = N.subtype ∘ₗ π' := rfl
  refine (injective_iff_map_eq_zero _).mpr fun t ht ↦ ?_
  obtain ⟨s, rfl⟩ := rTensor_surjective M hπ' t
  have hs : π.rTensor M ((N.comap π).subtype.rTensor M s) = 0 := by
    rw [← rTensor_comp_apply, hsq, rTensor_comp_apply, ht]
  obtain ⟨u, hu⟩ := (rTensor_exact M (exact_subtype_ker_map π) hπ _).mp hs
  have hker : ker π ≤ N.comap π := fun x hx ↦
    Submodule.mem_comap.mpr (mem_ker.mp hx ▸ N.zero_mem)
  have hsu : s = (Submodule.inclusion hker).rTensor M u := hG <| by
    rw [← hu, ← rTensor_comp_apply]
    rfl
  rw [hsu, ← rTensor_comp_apply]
  have : π' ∘ₗ Submodule.inclusion hker = 0 := by
    ext x
    exact mem_ker.mp x.2
  rw [this, rTensor_zero, LinearMap.zero_apply]

/-- If `L ⧸ N` is killed by `I`, then `N ⊗[R] M → L ⊗[R] M` is injective. -/
private theorem subtype_rTensor_injective_of_smul_top_le
    (hI : Function.Injective (I.subtype.rTensor M))
    {L : Type*} [AddCommGroup L] [Module R L] {N : Submodule R L} (hN : I • ⊤ ≤ N) :
    Function.Injective (N.subtype.rTensor M) :=
  subtype_rTensor_injective_of_surjective hI (π := Finsupp.linearCombination R id)
    (fun l ↦ ⟨Finsupp.single l 1, by simp⟩) hN

/-- If `L ⧸ N` is killed by `I ^ n`, then `N ⊗[R] M → L ⊗[R] M` is injective. -/
private theorem subtype_rTensor_injective_of_pow_smul_top_le
    (hI : Function.Injective (I.subtype.rTensor M))
    (n : ℕ) {L : Type*} [AddCommGroup L] [Module R L] {N : Submodule R L} (hN : I ^ n • ⊤ ≤ N) :
    Function.Injective (N.subtype.rTensor M) := by
  induction n generalizing N with
  | zero =>
    refine subtype_rTensor_injective_of_smul_top_le hI (le_trans ?_ hN)
    rw [pow_zero, Ideal.one_eq_top]
    exact Submodule.smul_mono_left le_top
  | succ n ih =>
    -- `N ⊆ N' = N + Iⁿ L ⊆ L`, where `I` kills `N' ⧸ N` and `Iⁿ` kills `L ⧸ N'`.
    set N' := N ⊔ I ^ n • ⊤
    have hle : N ≤ N' := le_sup_left
    have hN₀ : I • ⊤ ≤ N.comap N'.subtype := Submodule.smul_le.mpr fun i hi x _ ↦ by
      obtain ⟨y, hy, z, hz, hyz⟩ := Submodule.mem_sup.mp x.2
      have hiz : i • z ∈ I ^ (n + 1) • (⊤ : Submodule R L) := by
        rw [pow_succ', Submodule.mul_smul]
        exact Submodule.smul_mem_smul hi hz
      simpa [← hyz] using N.add_mem (N.smul_mem i hy) (hN hiz)
    have h₀ := subtype_rTensor_injective_of_smul_top_le hI hN₀
    have hsub : N.subtype = N'.subtype ∘ₗ (N.comap N'.subtype).subtype ∘ₗ
        (Submodule.comapSubtypeEquivOfLe hle).symm.toLinearMap := rfl
    rw [hsub, rTensor_comp, rTensor_comp, coe_comp, coe_comp]
    exact (ih le_sup_right).comp (h₀.comp (LinearEquiv.rTensor M _).injective)

/-- An element of the kernel of `J ⊗[R] M → M` comes from `(J ⊓ I ^ n) ⊗[R] M`. -/
private theorem mem_range_rTensor_inclusion (hI : Function.Injective (I.subtype.rTensor M)) (n : ℕ)
    {J : Ideal R} {t : J ⊗[R] M} (ht : J.subtype.rTensor M t = 0) :
    t ∈ range ((Submodule.inclusion (inf_le_left : J ⊓ I ^ n ≤ J)).rTensor M) := by
  -- `J ⧸ (J ⊓ Iⁿ)` is a submodule of `R ⧸ Iⁿ`, a module killed by `Iⁿ`.
  let P := I ^ n
  let N : Submodule R (R ⧸ P) := Submodule.map P.mkQ J
  let q : J →ₗ[R] N := (P.mkQ ∘ₗ J.subtype).codRestrict N fun j ↦ Submodule.mem_map_of_mem j.2
  have hq : Function.Surjective q := by
    rintro ⟨_, j, hj, rfl⟩
    exact ⟨⟨j, hj⟩, rfl⟩
  have hexact : Function.Exact (Submodule.inclusion (inf_le_left : J ⊓ P ≤ J)) q := by
    intro j
    rw [← Subtype.coe_inj, ZeroMemClass.coe_zero]
    simp only [q, codRestrict_apply, coe_comp, Function.comp_apply, Submodule.mkQ_apply,
      Submodule.coe_subtype, Submodule.Quotient.mk_eq_zero]
    exact ⟨fun h ↦ ⟨⟨j, j.2, h⟩, rfl⟩, fun ⟨x, hx⟩ ↦ hx ▸ x.2.2⟩
  have hPN : P • ⊤ ≤ N := Submodule.smul_le.mpr fun r hr x _ ↦ by
    obtain ⟨x, rfl⟩ := P.mkQ_surjective x
    rw [← map_smul, Submodule.mkQ_apply, (Submodule.Quotient.mk_eq_zero P).mpr
      (by simpa [smul_eq_mul] using P.mul_mem_right x hr)]
    exact N.zero_mem
  have hN := subtype_rTensor_injective_of_pow_smul_top_le hI n hPN
  refine (rTensor_exact M hexact hq t).mp (hN ?_)
  rw [← rTensor_comp_apply, map_zero]
  have : N.subtype ∘ₗ q = P.mkQ ∘ₗ J.subtype := rfl
  rw [this, rTensor_comp_apply, ht, map_zero]

/-- **Local criterion for flatness** (Stacks, Tag 00MK). Let `R` and `S` be Noetherian, `M` a finite
`S`-module and `I` an ideal of `R` with `I S` in the Jacobson radical of `S`. If `I ⊗[R] M → M` is
injective, that is `Tor₁ᴿ(R ⧸ I, M) = 0`, and `M ⧸ I M` is flat over `R ⧸ I`, then `M` is flat over
`R`. -/
@[stacks 00MK "with `I S` in the Jacobson radical in place of a local homomorphism"]
theorem Flat.of_subtype_rTensor_injective [IsNoetherianRing R] {S : Type*} [CommRing S]
    [IsNoetherianRing S] [Algebra R S] [Module S M] [IsScalarTower R S M] [Module.Finite S M]
    (hIS : I.map (algebraMap R S) ≤ (⊥ : Ideal S).jacobson)
    (hI : Function.Injective (I.subtype.rTensor M)) : Flat R M := by
  refine Flat.iff_lTensor_injective'.mpr fun J ↦ (injective_iff_map_eq_zero _).mpr fun t ht ↦ ?_
  obtain ⟨k, hk⟩ := I.exists_pow_inf_eq_pow_smul (M := R) J
  -- By Artin–Rees, `t` is divisible by every power of `I` in `M ⊗[R] J`.
  have hmem (n : ℕ) : t ∈ (I ^ n • ⊤ : Submodule R (M ⊗[R] J)) := by
    have ht' : J.subtype.rTensor M (TensorProduct.comm R M J t) = 0 := by
      rw [← comm_comp_lTensor_comp_comm_eq, coe_comp, Function.comp_apply, coe_comp,
        Function.comp_apply, LinearEquiv.coe_coe, LinearEquiv.coe_coe, comm_comm, ht, map_zero]
    obtain ⟨u, hu⟩ := mem_range_rTensor_inclusion hI (n + k) ht'
    have htu : t = (Submodule.inclusion inf_le_left).lTensor M (TensorProduct.comm R _ M u) := by
      apply (TensorProduct.comm R M J).injective
      rw [← hu, ← comm_comp_lTensor_comp_comm_eq]
      rfl
    have hle : J ⊓ I ^ (n + k) ≤ I ^ n • J := fun c hc ↦ by
      have := hk (n + k) (Nat.le_add_left k n)
      rw [Nat.add_sub_cancel] at this
      have hc' : c ∈ I ^ (n + k) • (⊤ : Submodule R R) ⊓ J :=
        ⟨by simpa [smul_eq_mul, Ideal.mul_top] using hc.2, hc.1⟩
      rw [this] at hc'
      exact Submodule.smul_mono le_rfl inf_le_right hc'
    refine range_lTensor_inclusion_smul_le (I ^ n) J
      ⟨(Submodule.inclusion hle).lTensor M (TensorProduct.comm R _ M u), ?_⟩
    rw [← lTensor_comp_apply, htu]
    rfl
  -- Krull's intersection theorem for the finite `S`-module `J ⊗[R] M`.
  set IS := I.map (algebraMap R S)
  have hle (n : ℕ) : (I ^ n • ⊤ : Submodule R (M ⊗[R] J)) ≤
      (IS ^ n • (⊤ : Submodule S (M ⊗[R] J))).restrictScalars R := by
    rw [← Ideal.map_pow, Ideal.smul_restrictScalars, Submodule.restrictScalars_top]
  have hbot := Ideal.iInf_pow_smul_eq_bot_of_le_jacobson IS hIS (M := M ⊗[R] J)
  have : t ∈ ⨅ n : ℕ, IS ^ n • (⊤ : Submodule S (M ⊗[R] J)) :=
    Submodule.mem_iInf _ |>.mpr fun n ↦ hle n (hmem n)
  simpa [hbot] using this

end

/-- If an `S`-module `M` is flat over `R`, then `Tor₁ˢ(S ⧸ J S, M) = 0` for every ideal `J` of `R`:
the map `J S ⊗[S] M → M` is injective. -/
theorem Flat.subtype_rTensor_injective_map {S : Type*} [CommRing S] [Algebra R S] [Module S M]
    [IsScalarTower R S M] [Flat R M] (J : Ideal R) :
    Function.Injective ((J.map (algebraMap R S)).subtype.rTensor M) := by
  rw [← lTensor_inj_iff_rTensor_inj]
  -- `M ⊗[S] (S ⊗[R] J) → M ⊗[S] J S → M` is `M ⊗[R] J → M`, and `S ⊗[R] J → J S` is onto.
  let ψ := (Algebra.idealMap S J).liftBaseChange S
  let e := AlgebraTensorModule.cancelBaseChange R S S M J
  have key (x : M ⊗[S] (S ⊗[R] J)) :
      TensorProduct.rid S M ((J.map (algebraMap R S)).subtype.lTensor M (ψ.lTensor M x)) =
        TensorProduct.rid R M (J.subtype.lTensor M (e x)) := by
    induction x using TensorProduct.inductionOn with
    | add x y hx hy => simp only [map_add, hx, hy]
    | tmul m y =>
      induction y using TensorProduct.inductionOn with
      | add y z hy hz => simp only [tmul_add, map_add, hy, hz]
      | tmul s j =>
        simpa [ψ, e, algebraMap_smul] using smul_comm s (j : R) m
  have hinj : Function.Injective
      (TensorProduct.rid S M ∘ (J.map (algebraMap R S)).subtype.lTensor M ∘ ψ.lTensor M) := by
    have : (TensorProduct.rid S M ∘ (J.map (algebraMap R S)).subtype.lTensor M ∘ ψ.lTensor M) =
        TensorProduct.rid R M ∘ J.subtype.lTensor M ∘ e := funext key
    rw [this]
    exact (TensorProduct.rid R M).injective.comp
      ((Flat.lTensor_preserves_injective_linearMap _ J.injective_subtype).comp e.injective)
  exact (Function.Injective.of_comp hinj).of_comp_right
    (lTensor_surjective M (Ideal.liftBaseChange_idealMap_surjective S J))

/-- **Flatness over the fibres** (Stacks, Tag 00MP). Let `R → S → T` be ring maps with `S` and `T`
Noetherian, let `M` be a finite `T`-module which is flat over `R`, and let `J` be an ideal of `R`
with `J T` in the Jacobson radical of `T`. If `M ⧸ J M` is flat over `S ⧸ J S`, then `M` is flat
over `S`. -/
@[stacks 00MP "with `J T` in the Jacobson radical in place of local homomorphisms"]
theorem Flat.of_flat_quotient_map {S T : Type*} [CommRing S] [IsNoetherianRing S]
    [Algebra R S] [Module S M] [IsScalarTower R S M] [CommRing T] [IsNoetherianRing T]
    [Algebra S T] [Module T M] [IsScalarTower S T M] [Module.Finite T M] [Flat R M] {J : Ideal R}
    (hJ : (J.map (algebraMap R S)).map (algebraMap S T) ≤ (⊥ : Ideal T).jacobson)
    [Flat (S ⧸ J.map (algebraMap R S)) (M ⧸ J.map (algebraMap R S) • (⊤ : Submodule S M))] :
    Flat S M :=
  of_subtype_rTensor_injective hJ (subtype_rTensor_injective_map J)

/-! ### Along a regular element -/

/-- If `x` is `M`-regular, then `Tor₁ᴿ(R ⧸ (x), M) = 0`: the map `(x) ⊗[R] M → M` is injective. -/
theorem _root_.IsSMulRegular.subtype_rTensor_injective_span {x : R} (reg : IsSMulRegular M x) :
    Function.Injective ((Ideal.span {x}).subtype.rTensor M) := by
  let x' : Ideal.span {x} := ⟨x, Ideal.mem_span_singleton_self x⟩
  have h (t : Ideal.span {x} ⊗[R] M) : ∃ m, t = x' ⊗ₜ m := by
    induction t using TensorProduct.inductionOn with
    | tmul y m =>
      obtain ⟨a, ha⟩ := Ideal.mem_span_singleton'.mp y.2
      exact ⟨a • m, by rw [← smul_tmul]; congr 1; ext; simp [x', ← ha]⟩
    | add t u ht hu =>
      obtain ⟨m, rfl⟩ := ht
      obtain ⟨n, rfl⟩ := hu
      exact ⟨m + n, (tmul_add _ _ _).symm⟩
  refine (injective_iff_map_eq_zero _).mpr fun t ht ↦ ?_
  obtain ⟨m, rfl⟩ := h t
  have : x • m = 0 := by simpa [x'] using congr(TensorProduct.lid R M $ht)
  rw [reg (this.trans (smul_zero x).symm), tmul_zero]

variable {x : R}

/-- **Local criterion for flatness** along a regular element (Stacks, Tag 00ML, for the ideal
`(x)`). Let `R` and `S` be Noetherian, `M` a finite `S`-module and `x ∈ R` with image in the
Jacobson radical of `S`. If `x` is `M`-regular and `M ⧸ x M` is flat over `R ⧸ (x)`, then `M` is
flat over `R`. -/
@[stacks 00ML "the case of a principal ideal"]
theorem Flat.of_flat_quotSMulTop [IsNoetherianRing R] {S : Type*} [CommRing S]
    [IsNoetherianRing S] [Algebra R S] [Module S M] [IsScalarTower R S M] [Module.Finite S M]
    (hx : algebraMap R S x ∈ (⊥ : Ideal S).jacobson) (reg : IsSMulRegular M x)
    [Flat (R ⧸ Ideal.span {x}) (QuotSMulTop x M)] : Flat R M := by
  have : Flat (R ⧸ Ideal.span {x}) (M ⧸ Ideal.span {x} • (⊤ : Submodule R M)) :=
    .of_linearEquiv ((Submodule.quotEquivOfEq _ _ (Submodule.ideal_span_singleton_smul x ⊤)
      ).extendScalarsOfSurjective Ideal.Quotient.mk_surjective)
  refine of_subtype_rTensor_injective (S := S) ?_ reg.subtype_rTensor_injective_span
  simpa [Ideal.map_span, Ideal.span_singleton_le_iff_mem] using hx

/-- **Local criterion for flatness** along a regular element, for a local homomorphism `R → S` of
Noetherian local rings (Stacks, Lemma 10.99.10 (00ML), for the ideal `(x)`): if `x` lies in the
maximal ideal of `R`, is `M`-regular, and `M ⧸ x M` is flat over `R ⧸ (x)`, then the finite
`S`-module `M` is flat over `R`. -/
@[stacks 00ML "the case of a principal ideal"]
theorem Flat.of_flat_quotSMulTop_of_isLocalHom [IsLocalRing R] [IsNoetherianRing R] {S : Type*}
    [CommRing S] [IsLocalRing S] [IsNoetherianRing S] [Algebra R S]
    [IsLocalHom (algebraMap R S)] [Module S M] [IsScalarTower R S M] [Module.Finite S M]
    (hx : x ∈ IsLocalRing.maximalIdeal R) (reg : IsSMulRegular M x)
    [Flat (R ⧸ Ideal.span {x}) (QuotSMulTop x M)] : Flat R M :=
  of_flat_quotSMulTop (S := S) (by
    rw [IsLocalRing.jacobson_eq_maximalIdeal ⊥ bot_ne_top]
    exact map_nonunit (algebraMap R S) x hx) reg

/-- For an `M`-regular element `x` as in `Module.Flat.of_flat_quotSMulTop`, `M ⧸ x M` is flat over
`R ⧸ (x)` if and only if `M` is flat over `R`. -/
theorem flat_quotSMulTop_iff_flat [IsNoetherianRing R] {S : Type*} [CommRing S]
    [IsNoetherianRing S] [Algebra R S] [Module S M] [IsScalarTower R S M] [Module.Finite S M]
    (hx : algebraMap R S x ∈ (⊥ : Ideal S).jacobson) (reg : IsSMulRegular M x) :
    Flat (R ⧸ Ideal.span {x}) (QuotSMulTop x M) ↔ Flat R M :=
  ⟨fun _ ↦ Flat.of_flat_quotSMulTop hx reg, fun _ ↦ inferInstance⟩

end Module

open IsLocalRing in
/-- Let `g : R → S` and `f : S → T` be ring homomorphisms of local rings, with `S` and `T`
Noetherian and `f` local. If `f ∘ g` is flat and `g` maps the maximal ideal of `R` onto a generating
set of the maximal ideal of `S`, then `f` is flat. This is flatness over the fibres
(`Module.Flat.of_flat_quotient_map`), whose fibre condition holds because `S ⧸ 𝔪_R S` is a field.
Unlike the module version, it applies to endomorphisms such as Frobenius. -/
theorem RingHom.Flat.of_comp_of_map_maximalIdeal_eq {R S T : Type*} [CommRing R] [IsLocalRing R]
    [CommRing S] [IsLocalRing S] [IsNoetherianRing S] [CommRing T] [IsLocalRing T]
    [IsNoetherianRing T] (g : R →+* S) (f : S →+* T) [IsLocalHom f] (hfg : (f.comp g).Flat)
    (hg : (maximalIdeal R).map g = maximalIdeal S) : f.Flat := by
  algebraize [g, f, f.comp g]
  let _ := Ideal.Quotient.field (maximalIdeal S)
  have : Module.Flat (S ⧸ maximalIdeal S) (T ⧸ maximalIdeal S • (⊤ : Submodule S T)) :=
    inferInstance
  have hg' : (maximalIdeal R).map (algebraMap R S) = maximalIdeal S := hg
  rw [← hg'] at this
  refine Module.Flat.of_flat_quotient_map (R := R) (M := T) (T := T) (J := maximalIdeal R) ?_
  rw [IsLocalRing.jacobson_eq_maximalIdeal ⊥ bot_ne_top]
  exact (Ideal.map_mono hg.le).trans (map_maximalIdeal_le f)
