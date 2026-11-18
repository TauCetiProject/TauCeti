/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.Analysis.Calculus.IteratedFDeriv.Prod
public import TauCeti.Analysis.Calculus.IteratedFDeriv.Symmetric
public import TauCeti.Analysis.Calculus.Jet.Equivalence
public import TauCeti.Analysis.Calculus.Jet.Realization
public import Mathlib.Analysis.Calculus.ContDiff.FiniteDimension
public import TauCeti.Topology.Algebra.Module.FiniteDimension

/-!
# Coordinate transformations of finite jets

The `k`-jet of a map `f : E → F` at `x` is the family `finiteJet 𝕜 k f x` of its iterated
derivatives of orders `0, …, k` at `x`, an element of
`FiniteJet 𝕜 E F k = Π i ≤ k, E [×i]→L[𝕜] F`. Over `ℝ` or `ℂ` the jets of `C^k` maps are
symmetric (`TauCeti.symmetricFiniteJets`), and every symmetric jet is the jet of its finite
Taylor polynomial (`TauCeti.finiteJet_finiteJetPolynomial_self`).

In local coordinates of a vector bundle, a change of base coordinates `h : E' → E` and a varying
linear change of fibre coordinates `g : E' → F →L[𝕜] G` turn a local section `s : E → F` into
`y ↦ g y (s (h y))`. By the higher chain and product rules, the `k`-jet of the new section at `x`
depends only on the `k`-jets of `g` and `h` at `x` and on the `k`-jet of `s` at `h x`, and it does
so linearly in the jet of `s`. The linear map `TauCeti.finiteJetPullback a b` realizes this
dependence: for jets `a` of `g` and `b` of `h` at `0`, it sends a jet `A` at `h 0` to the `k`-jet
at `0` of the transformed Taylor polynomials. The main results are:

* `TauCeti.finiteJet_clm_apply_comp`: the **chain rule for finite jets**. On finite-dimensional
  real spaces, `j^k_x (y ↦ g y (s (h y))) = finiteJetPullback (j^k_x g) (j^k_x h) (j^k_{h x} s)`
  for maps `g`, `h`, `s` that are `C^k` near the relevant points.
* `TauCeti.finiteJetPullback_finiteJet_id` and `TauCeti.finiteJetPullback_finiteJet_comp`: the
  identity and composition laws on symmetric jets, the cocycle conditions for coordinate changes.
* `TauCeti.finiteJetTruncation_finiteJetPullback`: the transformations commute with truncation of
  jets to lower order.
* `TauCeti.contDiff_finiteJetPullback`: the transformation depends smoothly on the jets of the
  coordinate changes. By `TauCeti.contDiffOn_toContinuousLinearMap_finiteJetPullback_finiteJet`,
  a `C^∞` family of coordinate changes on an open set gives a `C^∞` family of continuous linear
  maps between jet spaces.

The first-order analogue, written in the coordinates `F × (E →L[𝕜] F)`, is
`ContinuousLinearMap.firstJetPullback`, from which `TauCeti.FirstJetBundle` is glued. The
transformations here provide the coordinate changes from which a bundle of `k`-jets of a vector
bundle is glued in the same way.

## References

* I. Kolář, P. W. Michor and J. Slovák, *Natural Operations in Differential Geometry*,
  §§12.2–12.5 and §§12.16–12.17.
-/

public section

noncomputable section

open scoped ContDiff Topology

namespace TauCeti

section General

variable {𝕜 E E' E'' F G H : Type*} [NontriviallyNormedField 𝕜]
  [NormedAddCommGroup E] [NormedSpace 𝕜 E]
  [NormedAddCommGroup E'] [NormedSpace 𝕜 E']
  [NormedAddCommGroup E''] [NormedSpace 𝕜 E'']
  [NormedAddCommGroup F] [NormedSpace 𝕜 F]
  [NormedAddCommGroup G] [NormedSpace 𝕜 G]
  [NormedAddCommGroup H] [NormedSpace 𝕜 H]

/-! ### Finite jets -/

variable (𝕜 E F) in
/-- The coefficient space of `k`-jets of maps `E → F`: a continuous multilinear map
`E [×i]→L[𝕜] F` in each order `i ≤ k`. -/
abbrev FiniteJet (k : ℕ) : Type _ := (i : Fin (k + 1)) → E [×i.val]→L[𝕜] F

variable (𝕜) in
/-- The `k`-jet of `f` at `x`: the iterated derivatives of `f` at `x` of orders `0, …, k`, that is,
the truncation to these orders of Mathlib's Taylor series `ftaylorSeries 𝕜 f x`. -/
def finiteJet (k : ℕ) (f : E → F) (x : E) : FiniteJet 𝕜 E F k :=
  fun i ↦ iteratedFDeriv 𝕜 i f x

@[simp]
theorem finiteJet_apply (k : ℕ) (f : E → F) (x : E) (i : Fin (k + 1)) :
    finiteJet 𝕜 k f x i = iteratedFDeriv 𝕜 i f x :=
  (rfl)

/-- The order-zero coefficient of a jet evaluates to the value of the map. -/
theorem finiteJet_zero_apply (k : ℕ) (f : E → F) (x : E) (v : Fin 0 → E) :
    finiteJet 𝕜 k f x 0 v = f x :=
  iteratedFDeriv_zero_apply v

/-- Two maps have the same `k`-jet at `x` exactly when they agree to order `k` at `x`. -/
theorem finiteJet_eq_finiteJet_iff {k : ℕ} {f f' : E → F} {x : E} :
    finiteJet 𝕜 k f x = finiteJet 𝕜 k f' x ↔ SameJetAt 𝕜 k x f f' := by
  rw [sameJetAt_iff, funext_iff]
  exact ⟨fun h i hi ↦ h ⟨i, Nat.lt_succ_of_le hi⟩, fun h i ↦ h i (Nat.le_of_lt_succ i.isLt)⟩

/-- Jets commute with translations. -/
theorem finiteJet_comp_add_left (k : ℕ) (f : E → F) (a x : E) :
    finiteJet 𝕜 k (fun y ↦ f (a + y)) x = finiteJet 𝕜 k f (a + x) := by
  ext i : 1
  simp [iteratedFDeriv_comp_add_left]

variable (𝕜 E F) in
/-- The `k`-jets all of whose coefficients are symmetric multilinear maps. On finite-dimensional
real spaces the jets of `C^k` maps are symmetric (`ContDiffAt.finiteJet_mem_symmetricFiniteJets`),
and every symmetric jet is the jet of a polynomial (`TauCeti.finiteJet_finiteJetPolynomial_self`).
-/
def symmetricFiniteJets (k : ℕ) : Submodule 𝕜 (FiniteJet 𝕜 E F k) where
  carrier := {A | ∀ i (v : Fin i.val → E) (σ : Equiv.Perm (Fin i.val)), A i (v ∘ σ) = A i v}
  add_mem' ha hb i v σ := by simp [ha i v σ, hb i v σ]
  zero_mem' := by simp
  smul_mem' c A hA i v σ := by simp [hA i v σ]

/-- Membership in `TauCeti.symmetricFiniteJets`: every coefficient is invariant under permutations
of its arguments. -/
@[simp]
theorem mem_symmetricFiniteJets_iff {k : ℕ} {A : FiniteJet 𝕜 E F k} :
    A ∈ symmetricFiniteJets 𝕜 E F k ↔
      ∀ i (v : Fin i.val → E) (σ : Equiv.Perm (Fin i.val)), A i (v ∘ σ) = A i v :=
  Iff.rfl

/-- The jets of analytic maps are symmetric, over any field. -/
theorem _root_.ContDiffAt.finiteJet_mem_symmetricFiniteJets_of_omega {k : ℕ} {f : E → F}
    {x : E} (hf : ContDiffAt 𝕜 ω f x) : finiteJet 𝕜 k f x ∈ symmetricFiniteJets 𝕜 E F k :=
  fun _ v σ ↦ hf.iteratedFDeriv_comp_perm v σ

/-- A symmetric jet is the jet of its finite Taylor polynomial at the center. -/
theorem finiteJet_finiteJetPolynomial_self [CharZero 𝕜] {k : ℕ} {A : FiniteJet 𝕜 E F k}
    (hA : A ∈ symmetricFiniteJets 𝕜 E F k) (x : E) :
    finiteJet 𝕜 k (finiteJetPolynomial k A x) x = A := by
  ext i : 1
  exact iteratedFDeriv_finiteJetPolynomial_self k A x i (hA i)

/-- A map with a symmetric `k`-jet at `x` agrees to order `k` at `x` with the Taylor polynomial of
that jet. -/
theorem sameJetAt_finiteJetPolynomial_finiteJet [CharZero 𝕜] {k : ℕ} {f : E → F} {x : E}
    (hf : finiteJet 𝕜 k f x ∈ symmetricFiniteJets 𝕜 E F k) :
    SameJetAt 𝕜 k x f (finiteJetPolynomial k (finiteJet 𝕜 k f x) x) :=
  finiteJet_eq_finiteJet_iff.1 (finiteJet_finiteJetPolynomial_self hf x).symm

/-- On an open set, the `k`-jet of a `C^(n + k)` map is a `C^n` function of the point. -/
theorem _root_.ContDiffOn.finiteJet {k : ℕ} {n : ℕ∞ω} {f : E → F} {u : Set E} (hu : IsOpen u)
    (hf : ContDiffOn 𝕜 (n + k) f u) : ContDiffOn 𝕜 n (finiteJet 𝕜 k f) u := by
  refine contDiffOn_pi.2 fun i x hx ↦ ?_
  have hi : n + (i : ℕ) ≤ n + k := by gcongr; exact_mod_cast i.is_le
  exact ((hf.contDiffAt (hu.mem_nhds hx)).iteratedFDeriv_right hi).contDiffWithinAt

/-! ### Coordinate transformations of jets -/

/-- Finite Taylor polynomials with smoothly varying jets, centers and points vary smoothly. -/
private theorem contDiff_finiteJetPolynomial_comp {X D C : Type*} [NormedAddCommGroup X]
    [NormedSpace 𝕜 X] [NormedAddCommGroup D] [NormedSpace 𝕜 D] [NormedAddCommGroup C]
    [NormedSpace 𝕜 C] {k : ℕ} {n : ℕ∞ω} {A : X → FiniteJet 𝕜 D C k} {c y : X → D}
    (hA : ContDiff 𝕜 n A) (hc : ContDiff 𝕜 n c) (hy : ContDiff 𝕜 n y) :
    ContDiff 𝕜 n (fun q ↦ finiteJetPolynomial k (A q) (c q) (y q)) :=
  (contDiff_finiteJetPolynomial_uncurry k).comp (hA.prodMk (hc.prodMk hy))

/-- The composite of Taylor polynomials whose jet at `0` defines `TauCeti.finiteJetPullback`,
as a jointly smooth function of the three jets and the point. -/
private theorem contDiff_pullbackPolynomial {k : ℕ} {n : ℕ∞ω} :
    ContDiff 𝕜 n (fun q : (FiniteJet 𝕜 E' (F →L[𝕜] G) k × FiniteJet 𝕜 E' E k × FiniteJet 𝕜 E F k)
        × E' ↦ finiteJetPolynomial k q.1.1 0 q.2
          (finiteJetPolynomial k q.1.2.2 (q.1.2.1 0 0) (finiteJetPolynomial k q.1.2.1 0 q.2))) := by
  have hb : ContDiff 𝕜 n (fun q : (FiniteJet 𝕜 E' (F →L[𝕜] G) k × FiniteJet 𝕜 E' E k ×
      FiniteJet 𝕜 E F k) × E' ↦ q.1.2.1) := contDiff_fst.snd.fst
  have hb₀ : ContDiff 𝕜 n (fun q : (FiniteJet 𝕜 E' (F →L[𝕜] G) k × FiniteJet 𝕜 E' E k ×
      FiniteJet 𝕜 E F k) × E' ↦ q.1.2.1 0 0) :=
    (ContinuousMultilinearMap.apply 𝕜 (fun _ : Fin 0 ↦ E') E 0).contDiff.comp
      ((contDiff_apply 𝕜 (fun i : Fin (k + 1) ↦ E' [×i.val]→L[𝕜] E) 0).comp hb)
  exact (contDiff_finiteJetPolynomial_comp contDiff_fst.fst contDiff_const contDiff_snd).clm_apply
    (contDiff_finiteJetPolynomial_comp contDiff_fst.snd.snd hb₀
      (contDiff_finiteJetPolynomial_comp hb contDiff_const contDiff_snd))

/-- The transformation of `k`-jets of sections under a change of base coordinates and a varying
linear change of fibre coordinates, given by the `k`-jets `a` at `0` of the fibre maps
`g : E' → F →L[𝕜] G` and `b` at `0` of the base map `h : E' → E`. It sends a `k`-jet `A` at
`h 0 = b 0 0` to the `k`-jet at `0` of `y ↦ g y (s (h y))`, with the Taylor polynomials of `a`, `b`
and `A` in place of `g`, `h` and `s`. By the chain rule `TauCeti.finiteJet_clm_apply_comp`, it
computes the `k`-jet of the transformed section from the jets of actual coordinate changes and
sections. -/
def finiteJetPullback {k : ℕ} (a : FiniteJet 𝕜 E' (F →L[𝕜] G) k) (b : FiniteJet 𝕜 E' E k) :
    FiniteJet 𝕜 E F k →ₗ[𝕜] FiniteJet 𝕜 E' G k where
  toFun A := finiteJet 𝕜 k (fun y ↦ finiteJetPolynomial k a 0 y
    (finiteJetPolynomial k A (b 0 0) (finiteJetPolynomial k b 0 y))) 0
  map_add' A B := by
    have hd (C : FiniteJet 𝕜 E F k) := (contDiff_pullbackPolynomial (n := k)).comp
      ((contDiff_const (c := (a, b, C))).prodMk contDiff_id) |>.contDiffAt (x := (0 : E'))
    ext i : 1
    simp only [finiteJet_apply, finiteJetPolynomial_add, map_add, Pi.add_apply]
    exact iteratedFDeriv_add_apply ((hd A).of_le (by exact_mod_cast i.is_le))
      ((hd B).of_le (by exact_mod_cast i.is_le))
  map_smul' c A := by
    have hd := (contDiff_pullbackPolynomial (n := k)).comp
      ((contDiff_const (c := (a, b, A))).prodMk contDiff_id) |>.contDiffAt (x := (0 : E'))
    ext i : 1
    simp only [finiteJet_apply, finiteJetPolynomial_smul, map_smul, Pi.smul_apply,
      RingHom.id_apply]
    exact iteratedFDeriv_const_smul_apply' (hd.of_le (by exact_mod_cast i.is_le))

/-- The transformed jet is the jet at `0` of the transformed Taylor polynomials. -/
theorem finiteJetPullback_apply {k : ℕ} (a : FiniteJet 𝕜 E' (F →L[𝕜] G) k)
    (b : FiniteJet 𝕜 E' E k) (A : FiniteJet 𝕜 E F k) :
    finiteJetPullback a b A = finiteJet 𝕜 k (fun y ↦ finiteJetPolynomial k a 0 y
      (finiteJetPolynomial k A (b 0 0) (finiteJetPolynomial k b 0 y))) 0 :=
  (rfl)

/-- The transformed jets are symmetric: they are jets of polynomial maps. -/
theorem finiteJetPullback_mem_symmetricFiniteJets {k : ℕ} (a : FiniteJet 𝕜 E' (F →L[𝕜] G) k)
    (b : FiniteJet 𝕜 E' E k) (A : FiniteJet 𝕜 E F k) :
    finiteJetPullback a b A ∈ symmetricFiniteJets 𝕜 E' G k :=
  ContDiffAt.finiteJet_mem_symmetricFiniteJets_of_omega <| ((contDiff_pullbackPolynomial
    (n := ω)).comp ((contDiff_const (c := (a, b, A))).prodMk contDiff_id)).contDiffAt

/-- **The chain rule for finite jets.** The `k`-jet at `x` of `y ↦ g y (s (h y))` is the
transformation by the `k`-jets of `g` and `h` at `x` of the `k`-jet of `s` at `h x`, provided these
jets are symmetric. Over `ℝ` and on finite-dimensional spaces the symmetry is automatic
(`TauCeti.finiteJet_clm_apply_comp`). -/
theorem finiteJet_clm_apply_comp_of_mem [CharZero 𝕜] {k : ℕ} {g : E' → F →L[𝕜] G} {h : E' → E}
    {s : E → F} {x : E'} (hg : ContDiffAt 𝕜 k g x) (hh : ContDiffAt 𝕜 k h x)
    (hs : ContDiffAt 𝕜 k s (h x)) (hgs : finiteJet 𝕜 k g x ∈ symmetricFiniteJets 𝕜 E' _ k)
    (hhs : finiteJet 𝕜 k h x ∈ symmetricFiniteJets 𝕜 E' E k)
    (hss : finiteJet 𝕜 k s (h x) ∈ symmetricFiniteJets 𝕜 E F k) :
    finiteJet 𝕜 k (fun y ↦ g y (s (h y))) x =
      finiteJetPullback (finiteJet 𝕜 k g x) (finiteJet 𝕜 k h x) (finiteJet 𝕜 k s (h x)) := by
  set a := finiteJet 𝕜 k g x
  set b := finiteJet 𝕜 k h x
  set A := finiteJet 𝕜 k s (h x)
  -- Translate the base point to `0` and replace `g`, `h` and `s` by their Taylor polynomials,
  -- which have the same jets at the relevant points.
  have hgx : ContDiffAt 𝕜 k (fun y ↦ g (x + y)) 0 :=
    (by rwa [add_zero] : ContDiffAt 𝕜 k g (x + 0)).comp 0 (contDiffAt_const.add contDiffAt_id)
  have hhx : ContDiffAt 𝕜 k (fun y ↦ h (x + y)) 0 :=
    (by rwa [add_zero] : ContDiffAt 𝕜 k h (x + 0)).comp 0 (contDiffAt_const.add contDiffAt_id)
  have hsx : ContDiffAt 𝕜 k s (h (x + 0)) := by rwa [add_zero]
  have hPa : ContDiffAt 𝕜 k (finiteJetPolynomial k a 0) 0 :=
    (contDiff_finiteJetPolynomial k a 0).contDiffAt
  have hPb : ContDiffAt 𝕜 k (finiteJetPolynomial k b 0) 0 :=
    (contDiff_finiteJetPolynomial k b 0).contDiffAt
  have hPA : ContDiffAt 𝕜 k (finiteJetPolynomial k A (b 0 0)) (finiteJetPolynomial k b 0 0) :=
    (contDiff_finiteJetPolynomial k A _).contDiffAt
  have hg' : SameJetAt 𝕜 k 0 (fun y ↦ g (x + y)) (finiteJetPolynomial k a 0) := by
    simpa only [finiteJet_comp_add_left, add_zero] using
      sameJetAt_finiteJetPolynomial_finiteJet (x := 0) (f := fun y ↦ g (x + y))
        (by rwa [finiteJet_comp_add_left, add_zero])
  have hh' : SameJetAt 𝕜 k 0 (fun y ↦ h (x + y)) (finiteJetPolynomial k b 0) := by
    simpa only [finiteJet_comp_add_left, add_zero] using
      sameJetAt_finiteJetPolynomial_finiteJet (x := 0) (f := fun y ↦ h (x + y))
        (by rwa [finiteJet_comp_add_left, add_zero])
  have hb₀ : b 0 0 = h x := finiteJet_zero_apply k h x 0
  have hs' : SameJetAt 𝕜 k (h (x + 0)) s (finiteJetPolynomial k A (b 0 0)) := by
    rw [hb₀, add_zero]
    exact sameJetAt_finiteJetPolynomial_finiteJet hss
  have hsh := hh'.comp hs' hhx hPb hsx hPA
  have hpair := hg'.prodMk hsh hgx hPa (hsx.comp 0 hhx) (hPA.comp 0 hPb)
  have hev : ContDiff 𝕜 k (fun p : (F →L[𝕜] G) × F ↦ p.1 p.2) :=
    isBoundedBilinearMap_apply.contDiff
  have hjet := hpair.comp (SameJetAt.refl _ _) (hgx.prodMk (hsx.comp 0 hhx))
    (hPa.prodMk (hPA.comp 0 hPb)) hev.contDiffAt hev.contDiffAt
  have htr := finiteJet_comp_add_left (𝕜 := 𝕜) k (fun y ↦ g y (s (h y))) x 0
  rw [add_zero] at htr
  rw [← htr, finiteJetPullback_apply, finiteJet_eq_finiteJet_iff]
  exact hjet

/-- Constant identity fibre maps and the identity base map act identically on symmetric jets. -/
theorem finiteJetPullback_finiteJet_id [CharZero 𝕜] {k : ℕ} {A : FiniteJet 𝕜 E F k}
    (hA : A ∈ symmetricFiniteJets 𝕜 E F k) (x : E) :
    finiteJetPullback (finiteJet 𝕜 k (fun _ : E ↦ ContinuousLinearMap.id 𝕜 F) x)
      (finiteJet 𝕜 k id x) A = A := by
  have hpoly : ContDiff 𝕜 ω (finiteJetPolynomial k A x) := contDiff_finiteJetPolynomial k A x
  have h := finiteJet_clm_apply_comp_of_mem (k := k) (g := fun _ : E ↦ ContinuousLinearMap.id 𝕜 F)
    (h := id) (s := finiteJetPolynomial k A x) (x := x) contDiffAt_const contDiffAt_id
    (hpoly.contDiffAt.of_le le_top) contDiffAt_const.finiteJet_mem_symmetricFiniteJets_of_omega
    contDiffAt_id.finiteJet_mem_symmetricFiniteJets_of_omega
    hpoly.contDiffAt.finiteJet_mem_symmetricFiniteJets_of_omega
  simp only [ContinuousLinearMap.id_apply, id_eq] at h
  rw [finiteJet_finiteJetPolynomial_self hA] at h
  exact h.symm

/-! ### Truncation -/

variable (𝕜 E F) in
/-- The truncation of `m`-jets to `k`-jets for `k ≤ m`, forgetting the coefficients of orders
above `k`. -/
def finiteJetTruncation {k m : ℕ} (hkm : k ≤ m) : FiniteJet 𝕜 E F m →L[𝕜] FiniteJet 𝕜 E F k :=
  ContinuousLinearMap.pi fun i ↦ ContinuousLinearMap.proj (Fin.castLE (by omega) i)

@[simp]
theorem finiteJetTruncation_apply {k m : ℕ} (hkm : k ≤ m) (A : FiniteJet 𝕜 E F m)
    (i : Fin (k + 1)) : finiteJetTruncation 𝕜 E F hkm A i = A (Fin.castLE (by omega) i) :=
  (rfl)

/-- Truncating the `m`-jet of a map gives its `k`-jet. -/
@[simp]
theorem finiteJetTruncation_finiteJet {k m : ℕ} (hkm : k ≤ m) (f : E → F) (x : E) :
    finiteJetTruncation 𝕜 E F hkm (finiteJet 𝕜 m f x) = finiteJet 𝕜 k f x :=
  (rfl)

/-- Truncation maps symmetric jets to symmetric jets. -/
theorem finiteJetTruncation_mem_symmetricFiniteJets {k m : ℕ} (hkm : k ≤ m)
    {A : FiniteJet 𝕜 E F m} (hA : A ∈ symmetricFiniteJets 𝕜 E F m) :
    finiteJetTruncation 𝕜 E F hkm A ∈ symmetricFiniteJets 𝕜 E F k :=
  fun i v σ ↦ hA (Fin.castLE (by omega) i) v σ

/-- The `k`-jet of the Taylor polynomial of a symmetric `m`-jet is its truncation. -/
theorem finiteJet_finiteJetPolynomial_self_eq_finiteJetTruncation [CharZero 𝕜] {k m : ℕ}
    (hkm : k ≤ m) {A : FiniteJet 𝕜 E F m} (hA : A ∈ symmetricFiniteJets 𝕜 E F m) (x : E) :
    finiteJet 𝕜 k (finiteJetPolynomial m A x) x = finiteJetTruncation 𝕜 E F hkm A := by
  rw [← finiteJetTruncation_finiteJet hkm, finiteJet_finiteJetPolynomial_self hA]

/-- The transformations of jets commute with truncation, on symmetric jets. -/
theorem finiteJetTruncation_finiteJetPullback [CharZero 𝕜] {k m : ℕ} (hkm : k ≤ m)
    {a : FiniteJet 𝕜 E' (F →L[𝕜] G) m} {b : FiniteJet 𝕜 E' E m} {A : FiniteJet 𝕜 E F m}
    (ha : a ∈ symmetricFiniteJets 𝕜 E' _ m) (hb : b ∈ symmetricFiniteJets 𝕜 E' E m)
    (hA : A ∈ symmetricFiniteJets 𝕜 E F m) :
    finiteJetTruncation 𝕜 E' G hkm (finiteJetPullback a b A) =
      finiteJetPullback (finiteJetTruncation 𝕜 E' _ hkm a) (finiteJetTruncation 𝕜 E' E hkm b)
        (finiteJetTruncation 𝕜 E F hkm A) := by
  -- Realize the three jets by their Taylor polynomials and apply the chain rule in order `k`.
  have hg : ContDiff 𝕜 ω (finiteJetPolynomial m a 0) := contDiff_finiteJetPolynomial m a 0
  have hh : ContDiff 𝕜 ω (finiteJetPolynomial m b 0) := contDiff_finiteJetPolynomial m b 0
  have hs : ContDiff 𝕜 ω (finiteJetPolynomial m A (b 0 0)) := contDiff_finiteJetPolynomial m A _
  have hb₀ : finiteJetPolynomial m b 0 0 = b 0 0 := finiteJetPolynomial_self m b 0
  have hchain := finiteJet_clm_apply_comp_of_mem (k := k) (x := (0 : E'))
    (hg.contDiffAt.of_le le_top) (hh.contDiffAt.of_le le_top)
    (hs.contDiffAt.of_le le_top) hg.contDiffAt.finiteJet_mem_symmetricFiniteJets_of_omega
    hh.contDiffAt.finiteJet_mem_symmetricFiniteJets_of_omega
    hs.contDiffAt.finiteJet_mem_symmetricFiniteJets_of_omega
  rw [hb₀, finiteJet_finiteJetPolynomial_self_eq_finiteJetTruncation hkm ha,
    finiteJet_finiteJetPolynomial_self_eq_finiteJetTruncation hkm hb,
    finiteJet_finiteJetPolynomial_self_eq_finiteJetTruncation hkm hA] at hchain
  rw [← hchain, finiteJetPullback_apply, finiteJetTruncation_finiteJet]

/-! ### Smooth dependence on the coordinate changes -/

/-- The transformation of jets depends smoothly, in fact polynomially, on the jets of the
coordinate changes and on the transformed jet. -/
theorem contDiff_finiteJetPullback {k : ℕ} {n : ℕ∞ω} :
    ContDiff 𝕜 n (fun q : FiniteJet 𝕜 E' (F →L[𝕜] G) k × FiniteJet 𝕜 E' E k ×
      FiniteJet 𝕜 E F k ↦ finiteJetPullback q.1 q.2.1 q.2.2) := by
  refine contDiff_pi.2 fun i ↦ ?_
  simp only [finiteJetPullback_apply, finiteJet_apply]
  exact ((contDiff_pullbackPolynomial (n := ω)).contDiff_iteratedFDeriv_prod_right i
    le_top).comp (contDiff_id.prodMk contDiff_const)

/-- For finite-dimensional source jets, the transformation of jets is a smooth function of the
jets of the coordinate changes with values in continuous linear maps. -/
theorem contDiff_toContinuousLinearMap_finiteJetPullback [CompleteSpace 𝕜]
    [FiniteDimensional 𝕜 E] [FiniteDimensional 𝕜 F] {k : ℕ} {n : ℕ∞ω} :
    ContDiff 𝕜 n (fun p : FiniteJet 𝕜 E' (F →L[𝕜] G) k × FiniteJet 𝕜 E' E k ↦
      LinearMap.toContinuousLinearMap (finiteJetPullback p.1 p.2)) := by
  refine contDiff_clm_apply_iff.2 fun A ↦ ?_
  simp only [LinearMap.coe_toContinuousLinearMap']
  exact contDiff_finiteJetPullback.comp (contDiff_fst.prodMk (contDiff_snd.prodMk contDiff_const))

/-- A `C^(n + k)` family of coordinate changes on an open set gives a `C^n` family of
transformations of `k`-jets, as continuous linear maps. -/
theorem contDiffOn_toContinuousLinearMap_finiteJetPullback_finiteJet [CompleteSpace 𝕜]
    [FiniteDimensional 𝕜 E] [FiniteDimensional 𝕜 F] {k : ℕ} {n : ℕ∞ω} {g : E' → F →L[𝕜] G}
    {h : E' → E} {u : Set E'}
    (hu : IsOpen u) (hg : ContDiffOn 𝕜 (n + k) g u) (hh : ContDiffOn 𝕜 (n + k) h u) :
    ContDiffOn 𝕜 n (fun x ↦ LinearMap.toContinuousLinearMap
      (finiteJetPullback (finiteJet 𝕜 k g x) (finiteJet 𝕜 k h x))) u :=
  contDiff_toContinuousLinearMap_finiteJetPullback.comp_contDiffOn
    ((hg.finiteJet hu).prodMk (hh.finiteJet hu))

end General

/-! ### Real coefficients -/

section Real

variable {E E' E'' F G H : Type*}
  [NormedAddCommGroup E] [NormedSpace ℝ E] [FiniteDimensional ℝ E]
  [NormedAddCommGroup E'] [NormedSpace ℝ E'] [FiniteDimensional ℝ E']
  [NormedAddCommGroup E''] [NormedSpace ℝ E''] [FiniteDimensional ℝ E'']
  [NormedAddCommGroup F] [NormedSpace ℝ F]
  [NormedAddCommGroup G] [NormedSpace ℝ G]
  [NormedAddCommGroup H] [NormedSpace ℝ H]

/-- On a finite-dimensional real space, the `k`-jet of a map which is `C^k` near `x` is
symmetric. -/
theorem _root_.ContDiffAt.finiteJet_mem_symmetricFiniteJets {k : ℕ} {f : E → F} {x : E}
    (hf : ContDiffAt ℝ k f x) : finiteJet ℝ k f x ∈ symmetricFiniteJets ℝ E F k :=
  fun i v σ ↦ (hf.of_le (by exact_mod_cast i.is_le)).iteratedFDeriv_comp_perm_of_finiteDimensional
    v σ

/-- **The chain rule for finite jets.** On finite-dimensional real spaces, the `k`-jet at `x` of
`y ↦ g y (s (h y))` is the transformation by the `k`-jets of `g` and `h` at `x` of the `k`-jet of
`s` at `h x`, for maps `g` and `h` which are `C^k` near `x` and `s` which is `C^k` near `h x`. -/
theorem finiteJet_clm_apply_comp {k : ℕ} {g : E' → F →L[ℝ] G} {h : E' → E} {s : E → F} {x : E'}
    (hg : ContDiffAt ℝ k g x) (hh : ContDiffAt ℝ k h x) (hs : ContDiffAt ℝ k s (h x)) :
    finiteJet ℝ k (fun y ↦ g y (s (h y))) x =
      finiteJetPullback (finiteJet ℝ k g x) (finiteJet ℝ k h x) (finiteJet ℝ k s (h x)) :=
  finiteJet_clm_apply_comp_of_mem hg hh hs hg.finiteJet_mem_symmetricFiniteJets
    hh.finiteJet_mem_symmetricFiniteJets hs.finiteJet_mem_symmetricFiniteJets

/-- **The composition law for transformations of jets.** Transforming a symmetric jet first by
`(g₁, h₁)` at `h₂ x` and then by `(g₂, h₂)` at `x` is transforming it by the composite coordinate
change `(y ↦ g₂ y ∘L g₁ (h₂ y), h₁ ∘ h₂)` at `x`. This is the cocycle condition for gluing a bundle
of `k`-jets from these coordinate changes. -/
theorem finiteJetPullback_finiteJet_comp {k : ℕ} {g₁ : E' → F →L[ℝ] G} {h₁ : E' → E}
    {g₂ : E'' → G →L[ℝ] H} {h₂ : E'' → E'} {x : E''} (hg₁ : ContDiffAt ℝ k g₁ (h₂ x))
    (hh₁ : ContDiffAt ℝ k h₁ (h₂ x)) (hg₂ : ContDiffAt ℝ k g₂ x) (hh₂ : ContDiffAt ℝ k h₂ x)
    {A : FiniteJet ℝ E F k} (hA : A ∈ symmetricFiniteJets ℝ E F k) :
    finiteJetPullback (finiteJet ℝ k g₂ x) (finiteJet ℝ k h₂ x)
        (finiteJetPullback (finiteJet ℝ k g₁ (h₂ x)) (finiteJet ℝ k h₁ (h₂ x)) A) =
      finiteJetPullback (finiteJet ℝ k (fun y ↦ (g₂ y).comp (g₁ (h₂ y))) x)
        (finiteJet ℝ k (h₁ ∘ h₂) x) A := by
  -- Realize `A` as the jet of its Taylor polynomial `s` and apply the chain rule three times.
  set s := finiteJetPolynomial k A (h₁ (h₂ x))
  have hs : ContDiff ℝ k s := contDiff_finiteJetPolynomial k A _
  have hsA : finiteJet ℝ k s (h₁ (h₂ x)) = A := finiteJet_finiteJetPolynomial_self hA _
  have ht : ContDiffAt ℝ k (fun y ↦ g₁ y (s (h₁ y))) (h₂ x) :=
    hg₁.clm_apply (hs.contDiffAt.comp _ hh₁)
  rw [← hsA, ← finiteJet_clm_apply_comp hg₁ hh₁ hs.contDiffAt,
    ← finiteJet_clm_apply_comp hg₂ hh₂ ht]
  -- Both sides are jets of `y ↦ g₂ y (g₁ (h₂ y) (s (h₁ (h₂ y))))`.
  have h := finiteJet_clm_apply_comp (hg₂.clm_comp (hg₁.comp x hh₂)) (hh₁.comp x hh₂) hs.contDiffAt
  simp only [ContinuousLinearMap.comp_apply, Function.comp_apply] at h
  exact h

end Real

end TauCeti
